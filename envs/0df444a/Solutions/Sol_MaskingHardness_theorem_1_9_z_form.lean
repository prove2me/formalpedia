-- Prove2me | solution 1 for MaskingHardness.theorem_1_9_z_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:21:50.074253+00:00
-- url     : https://prove2.me/submissions/f721fe65-ecd7-4ad7-b1f6-2a551343874e

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_lossObjective

open MaskingHardness

namespace ZFormAux

lemma coe_fsum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (((∑ i ∈ s, f i : ℝ)) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma sum_eq_bot {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → EReal) (i : ι) (hi : i ∈ s)
    (hf : f i = ⊥) : ∑ j ∈ s, f j = ⊥ := by
  rw [← Finset.add_sum_erase s f hi, hf, EReal.bot_add]

section Hsec
variable {X : Type*} [Fintype X] {k : ℕ} (D : X → Fin k → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)

/-- the fidelity `E[h(y, z(x,y))]` -/
noncomputable def Hf (z : X → Fin k → Fin k → ℝ) : EReal :=
  ∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (z x y)

variable {D h}

lemma H_le (hD0 : ∀ x y, 0 ≤ D x y) (z : X → Fin k → Fin k → ℝ) (t : X → Fin k → ℝ)
    (ht : ∀ x y, h y (z x y) ≤ t x y) :
    Hf D h z ≤ ((∑ x, ∑ y, D x y * t x y : ℝ) : EReal) := by
  unfold Hf
  rw [coe_fsum]; apply Finset.sum_le_sum; intro x _
  rw [coe_fsum]; apply Finset.sum_le_sum; intro y _
  rw [EReal.coe_mul]
  exact mul_le_mul_of_nonneg_left (ht x y) (by exact_mod_cast hD0 x y)

lemma le_H (hD0 : ∀ x y, 0 ≤ D x y) (z : X → Fin k → Fin k → ℝ) (t : X → Fin k → ℝ)
    (ht : ∀ x y, 0 < D x y → (t x y : EReal) ≤ h y (z x y)) :
    ((∑ x, ∑ y, D x y * t x y : ℝ) : EReal) ≤ Hf D h z := by
  unfold Hf
  rw [coe_fsum]; apply Finset.sum_le_sum; intro x _
  rw [coe_fsum]; apply Finset.sum_le_sum; intro y _
  rw [EReal.coe_mul]
  rcases (hD0 x y).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · exact mul_le_mul_of_nonneg_left (ht x y hpos) (by exact_mod_cast hpos.le)

lemma H_bot (z : X → Fin k → Fin k → ℝ) (x₀ : X) (y₀ : Fin k) (hpos : 0 < D x₀ y₀)
    (hb : h y₀ (z x₀ y₀) = ⊥) : Hf D h z = ⊥ := by
  classical
  unfold Hf
  apply sum_eq_bot _ _ x₀ (Finset.mem_univ _)
  apply sum_eq_bot _ _ y₀ (Finset.mem_univ _)
  rw [hb]; exact EReal.coe_mul_bot_of_pos hpos

lemma H_real (hD0 : ∀ x y, 0 ≤ D x y) (htop : ∀ y b, h y b ≠ ⊤) (z : X → Fin k → Fin k → ℝ)
    (hnb : ∀ x y, 0 < D x y → h y (z x y) ≠ ⊥) :
    Hf D h z = ((∑ x, ∑ y, D x y * (h y (z x y)).toReal : ℝ) : EReal) := by
  apply le_antisymm
  · apply H_le hD0
    intro x y
    induction hb : h y (z x y) using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hb (htop _ _)
    | coe t => simp
  · apply le_H hD0
    intro x y hpos
    rw [EReal.coe_toReal (htop _ _) (hnb x y hpos)]

lemma H_ne_top (hD0 : ∀ x y, 0 ≤ D x y) (htop : ∀ y b, h y b ≠ ⊤) (z : X → Fin k → Fin k → ℝ) :
    Hf D h z ≠ ⊤ := by
  refine ne_top_of_le_ne_top (EReal.coe_ne_top _) (H_le hD0 z (fun x y => (h y (z x y)).toReal) ?_)
  intro x y
  induction hb : h y (z x y) using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hb (htop _ _)
  | coe t => simp

lemma H_nb_of_ne_bot (z : X → Fin k → Fin k → ℝ) (hH : Hf D h z ≠ ⊥) :
    ∀ x y, 0 < D x y → h y (z x y) ≠ ⊥ := by
  intro x y hpos hb
  exact hH (H_bot z x y hpos hb)

end Hsec

section Msec
variable {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ} (D : X → Fin k → ℝ)
  (c : ι → X → Fin k → ℝ)

/-- the masking statistic `E[⟨c_i(x), z(x,y) - 1/k⟩]` -/
noncomputable def mf (i : ι) (z : X → Fin k → Fin k → ℝ) : ℝ :=
  ∑ x, ∑ y, D x y * (c i x ⬝ᵥ (z x y - fun _ => (k : ℝ)⁻¹))

variable {D c}

omit [Fintype ι] in
lemma m_affine (i : ι) (z₁ z₂ : X → Fin k → Fin k → ℝ) (a b : ℝ) (hab : a + b = 1) :
    mf D c i (a • z₁ + b • z₂) = a * mf D c i z₁ + b * mf D c i z₂ := by
  unfold mf
  have : ∀ x y, (a • z₁ + b • z₂) x y - (fun _ => (k : ℝ)⁻¹) =
      a • (z₁ x y - fun _ => (k : ℝ)⁻¹) + b • (z₂ x y - fun _ => (k : ℝ)⁻¹) := by
    intro x y; funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination ((k : ℝ)⁻¹) * hab
  simp_rw [this, dotProduct_add, dotProduct_smul, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> (apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring)

omit [Fintype ι] in
lemma m_continuous (i : ι) : Continuous (fun z : X → Fin k → Fin k → ℝ => mf D c i z) := by
  unfold mf dotProduct; fun_prop

lemma centered_dot (v w : Fin k → ℝ) (hw : ∑ j, w j = 1) :
    centered v ⬝ᵥ w = v ⬝ᵥ (w - fun _ => (k : ℝ)⁻¹) := by
  simp only [centered, dotProduct, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hw, ← Finset.sum_mul]
  ring

lemma combo_sum (lam : ι → ℝ) (z : X → Fin k → Fin k → ℝ) :
    ∑ x, ∑ y, D x y * (combo c lam x ⬝ᵥ (z x y - fun _ => (k : ℝ)⁻¹)) =
      ∑ i, lam i * mf D c i z := by
  unfold mf combo
  simp_rw [sum_dotProduct, smul_dotProduct, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro i _
  ring

end Msec

lemma usc_fsum {α ι : Type*} [TopologicalSpace α] (s : Finset ι) (f : ι → α → EReal)
    (hf : ∀ i ∈ s, UpperSemicontinuous (f i)) (htop : ∀ i ∈ s, ∀ a, f i a ≠ ⊤) :
    UpperSemicontinuous (fun a => ∑ i ∈ s, f i a) ∧ ∀ a, ∑ i ∈ s, f i a ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨upperSemicontinuous_const, fun _ => EReal.zero_ne_top⟩
  | insert j s hj ih =>
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => htop i (Finset.mem_insert_of_mem hi))
    have hfj := hf j (Finset.mem_insert_self j s)
    have htj := htop j (Finset.mem_insert_self j s)
    simp only [Finset.sum_insert hj]
    refine ⟨?_, fun a => EReal.add_ne_top (htj a) (ih'.2 a)⟩
    apply UpperSemicontinuous.add' hfj ih'.1
    intro a
    exact EReal.continuousAt_add (Or.inl (htj a)) (Or.inr (ih'.2 a))

/-- multiplication by a nonnegative real preserves upper semicontinuity -/
lemma usc_coe_mul {α : Type*} [TopologicalSpace α] (d : ℝ) (hd : 0 ≤ d) (φ : α → EReal)
    (hφ : UpperSemicontinuous φ) : UpperSemicontinuous (fun a => (d : EReal) * φ a) := by
  rcases hd.eq_or_lt with h0 | hpos
  · subst h0; simp only [EReal.coe_zero, zero_mul]; exact upperSemicontinuous_const
  · intro a
    have hc : ContinuousAt (fun t : EReal => (d : EReal) * t) (φ a) := by
      have : (fun t : EReal => (d : EReal) * t) = (fun p : EReal × EReal => p.1 * p.2) ∘
          (fun t => ((d : EReal), t)) := rfl
      rw [this]
      apply ContinuousAt.comp
      · apply EReal.continuousAt_mul
        · left; simp [hpos.ne']
        · left; simp [hpos.ne']
        · left; simp
        · left; simp
      · fun_prop
    exact ContinuousAt.comp_upperSemicontinuousAt hc (hφ a)
      (fun s t hst => mul_le_mul_of_nonneg_left hst (by exact_mod_cast hpos.le))

lemma neg_lsc {α : Type*} [TopologicalSpace α] (φ : α → EReal) (hφ : UpperSemicontinuous φ) :
    LowerSemicontinuous (fun a => -φ a) := by
  intro a y hy
  have : φ a < -y := EReal.lt_neg_comm.mp hy
  filter_upwards [hφ a (-y) this] with a' ha'
  exact EReal.lt_neg_comm.mp ha'

section hfacts
variable {k : ℕ} {g : (Fin k → ℝ) → ℝ} {h : (Fin k → ℝ) → EReal}
  (hgh : IsConvConcConj (fun a => ((g a : ℝ) : EReal)) h)
include hgh

lemma h_inf (b : Fin k → ℝ) : h b = ⨅ a, ((g a + a ⬝ᵥ b : ℝ) : EReal) := by
  rw [hgh.2.1 b]; simp [EReal.coe_add]

lemma h_le (a b : Fin k → ℝ) : h b ≤ ((g a + a ⬝ᵥ b : ℝ) : EReal) := by
  rw [h_inf hgh b]; exact iInf_le _ a

lemma h_ne_top (b : Fin k → ℝ) : h b ≠ ⊤ := hgh.2.2.2.2.1 b

lemma h_le_toReal (b : Fin k → ℝ) : h b ≤ (((h b).toReal : ℝ) : EReal) := by
  induction hb : h b using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hb (h_ne_top hgh b)
  | coe t => simp

lemma h_usc : UpperSemicontinuous h := by
  rw [funext (h_inf hgh)]
  exact upperSemicontinuous_iInf
    (fun a => (continuous_coe_real_ereal.comp (by fun_prop)).upperSemicontinuous)

lemma h_concave (b₁ b₂ : Fin k → ℝ) (t₁ t₂ θ₁ θ₂ : ℝ) (h₁ : h b₁ = t₁) (h₂ : h b₂ = t₂)
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hθ : θ₁ + θ₂ = 1) :
    ((θ₁ * t₁ + θ₂ * t₂ : ℝ) : EReal) ≤ h (θ₁ • b₁ + θ₂ • b₂) := by
  rw [h_inf hgh]
  apply le_iInf
  intro a
  have e₁ : (t₁ : EReal) ≤ ((g a + a ⬝ᵥ b₁ : ℝ) : EReal) := h₁ ▸ h_le hgh a b₁
  have e₂ : (t₂ : EReal) ≤ ((g a + a ⬝ᵥ b₂ : ℝ) : EReal) := h₂ ▸ h_le hgh a b₂
  have e₁' : t₁ ≤ g a + a ⬝ᵥ b₁ := by exact_mod_cast e₁
  have e₂' : t₂ ≤ g a + a ⬝ᵥ b₂ := by exact_mod_cast e₂
  have m₁ := mul_le_mul_of_nonneg_left e₁' hθ₁
  have m₂ := mul_le_mul_of_nonneg_left e₂' hθ₂
  have : g a + a ⬝ᵥ (θ₁ • b₁ + θ₂ • b₂) = θ₁ * (g a + a ⬝ᵥ b₁) + θ₂ * (g a + a ⬝ᵥ b₂) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : g a = (θ₁ + θ₂) * g a := by rw [hθ, one_mul]
    linarith [this]
  exact_mod_cast (show θ₁ * t₁ + θ₂ * t₂ ≤ g a + a ⬝ᵥ (θ₁ • b₁ + θ₂ • b₂) by linarith)

lemma h_approx (hdom : ∀ z, z ∉ stdSimplex ℝ (Fin k) → h z = ⊥) (a : Fin k → ℝ) (δ : ℝ)
    (hδ : 0 < δ) : ∃ b ∈ stdSimplex ℝ (Fin k), ((g a - δ + a ⬝ᵥ b : ℝ) : EReal) < h b := by
  have hg : ((g a : ℝ) : EReal) = ⨆ b, h b - ((a ⬝ᵥ b : ℝ) : EReal) := hgh.1 a
  have : ((g a - δ : ℝ) : EReal) < ⨆ b, h b - ((a ⬝ᵥ b : ℝ) : EReal) := by
    rw [← hg]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨b, hb⟩ := lt_iSup_iff.mp this
  induction hb' : h b using EReal.rec with
  | bot => rw [hb'] at hb; simp at hb
  | top => exact absurd hb' (h_ne_top hgh b)
  | coe t =>
    rw [hb', ← EReal.coe_sub] at hb
    have hlt : g a - δ < t - a ⬝ᵥ b := by exact_mod_cast hb
    refine ⟨b, ?_, ?_⟩
    · by_contra hn; rw [hdom b hn] at hb'; exact EReal.bot_ne_coe t hb'
    · rw [hb']; exact EReal.coe_lt_coe_iff.mpr (by linarith)

end hfacts

end ZFormAux

open ZFormAux in
theorem solution {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y))
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest
      {v : EReal | ∃ z : X → Fin k → Fin k → ℝ,
        (∀ x y, z x y ∈ stdSimplex ℝ (Fin k)) ∧
        (∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ (z x y - fun _ => (k : ℝ)⁻¹))| ≤ ε) ∧
        v = ∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (z x y)}
      (⨅ lam : ι → ℝ, ((MaskingHardness.lossObjective D c g ε lam : ℝ) : EReal)) := by
  classical
  have hD0 := hD.1
  have htop : ∀ y b, h y b ≠ ⊤ := fun y b => h_ne_top (hgh y) b
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; have := hD.2; simp at this
    · exact h0
  set K : Set (X → Fin k → Fin k → ℝ) := {z | ∀ x y, z x y ∈ stdSimplex ℝ (Fin k)} with hK
  set Sf : Set (X → Fin k → Fin k → ℝ) := K ∩ {z | ∀ i, |mf D c i z| ≤ ε} with hSf
  set L : (ι → ℝ) → ℝ := fun lam => lossObjective D c g ε lam with hL
  set V : EReal := ⨅ lam : ι → ℝ, ((L lam : ℝ) : EReal) with hV
  set r : (X → Fin k → Fin k → ℝ) → (ι → ℝ) → ℝ :=
    fun z lam => ∑ i, lam i * mf D c i z - ε * ∑ i, |lam i| with hr
  set f : (X → Fin k → Fin k → ℝ) → (ι → ℝ) → EReal :=
    fun z lam => -Hf D h z + ((r z lam : ℝ) : EReal) with hf
  -- the compact convex set `K`
  have hKpi : K = Set.univ.pi (fun _ : X => Set.univ.pi (fun _ : Fin k => stdSimplex ℝ (Fin k))) := by
    ext z; simp [hK, Set.mem_pi]
  have hKc : IsCompact K := by
    rw [hKpi]; exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_stdSimplex _ _))
  have hKconv : Convex ℝ K := by
    rw [hKpi]; exact convex_pi (fun _ _ => convex_pi (fun _ _ => convex_stdSimplex ℝ _))
  -- the uniform point
  set z₀ : X → Fin k → Fin k → ℝ := fun _ _ _ => (k : ℝ)⁻¹ with hz₀
  have hz₀K : z₀ ∈ K := by
    intro x y
    refine ⟨fun i => inv_nonneg.mpr (Nat.cast_nonneg k), ?_⟩
    simp [hz₀]
    field_simp
  have hz₀m : ∀ i, mf D c i z₀ = 0 := by
    intro i; unfold mf
    have : ∀ x y, z₀ x y - (fun _ => (k : ℝ)⁻¹) = 0 := by intro x y; funext j; simp [hz₀]
    simp [this]
  have hz₀S : z₀ ∈ Sf := ⟨hz₀K, fun i => by rw [hz₀m i]; simpa using hε⟩
  -- simplex sums
  have hsum1 : ∀ z ∈ K, ∀ x y, ∑ j, z x y j = 1 := fun z hz x y => (hz x y).2
  -- the key identity
  have hkey : ∀ z ∈ K, ∀ lam : ι → ℝ,
      ∑ x, ∑ y, D x y * (centered (combo c lam x) ⬝ᵥ z x y) = ∑ i, lam i * mf D c i z := by
    intro z hz lam
    rw [← combo_sum]
    apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _
    rw [centered_dot _ _ (hsum1 z hz x y)]
  -- weak duality
  have hweak : ∀ z ∈ Sf, ∀ lam, Hf D h z ≤ ((L lam : ℝ) : EReal) := by
    intro z hz lam
    refine (H_le hD0 z (fun x y => g y (centered (combo c lam x)) +
      centered (combo c lam x) ⬝ᵥ z x y) (fun x y => h_le (hgh y) _ _)).trans
      (EReal.coe_le_coe_iff.mpr ?_)
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hkey z hz.1 lam]
    simp only [hL, lossObjective]
    have : ∑ i, lam i * mf D c i z ≤ ε * ∑ i, |lam i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro i _
      calc lam i * mf D c i z ≤ |lam i * mf D c i z| := le_abs_self _
        _ = |lam i| * |mf D c i z| := abs_mul _ _
        _ ≤ |lam i| * ε := mul_le_mul_of_nonneg_left (hz.2 i) (abs_nonneg _)
        _ = ε * |lam i| := mul_comm _ _
    linarith
  -- upper semicontinuity of the fidelity
  have hterm_ne_top : ∀ (z : X → Fin k → Fin k → ℝ) x y,
      ((D x y : ℝ) : EReal) * h y (z x y) ≠ ⊤ := by
    intro z x y
    refine ne_top_of_le_ne_top (EReal.coe_ne_top (D x y * (h y (z x y)).toReal)) ?_
    rw [EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (h_le_toReal (hgh y) _) (by exact_mod_cast hD0 x y)
  have hHusc : UpperSemicontinuous (Hf D h) := by
    have := usc_fsum (Finset.univ : Finset X)
      (fun x (z : X → Fin k → Fin k → ℝ) => ∑ y, ((D x y : ℝ) : EReal) * h y (z x y))
      (fun x _ => (usc_fsum (Finset.univ : Finset (Fin k))
        (fun y (z : X → Fin k → Fin k → ℝ) => ((D x y : ℝ) : EReal) * h y (z x y))
        (fun y _ => usc_coe_mul _ (hD0 x y) _
          ((h_usc (hgh y)).comp (show Continuous (fun z : X → Fin k → Fin k → ℝ => z x y) by
            fun_prop)))
        (fun y _ z => hterm_ne_top z x y)).1)
      (fun x _ z => (usc_fsum (Finset.univ : Finset (Fin k))
        (fun y (z : X → Fin k → Fin k → ℝ) => ((D x y : ℝ) : EReal) * h y (z x y))
        (fun y _ => usc_coe_mul _ (hD0 x y) _
          ((h_usc (hgh y)).comp (show Continuous (fun z : X → Fin k → Fin k → ℝ => z x y) by
            fun_prop)))
        (fun y _ z => hterm_ne_top z x y)).2 z)
    exact this.1
  -- the feasible set is compact, and the fidelity attains its maximum there
  have hSc : IsCompact Sf := by
    apply hKc.inter_right
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (m_continuous i).abs continuous_const
  obtain ⟨zs, hzsS, hzsmax⟩ :=
    (hHusc.upperSemicontinuousOn Sf).exists_isMaxOn ⟨z₀, hz₀S⟩ hSc
  -- continuity of `r` in each variable
  have hr_cont_z : ∀ lam, Continuous (fun z => r z lam) := by
    intro lam
    simp only [hr]
    exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (m_continuous i))).sub
      continuous_const
  have hr_cont_l : ∀ z, Continuous (fun lam => r z lam) := by
    intro z; simp only [hr]; fun_prop
  -- lower semicontinuity in `z`
  have hfy : ∀ lam ∈ (Set.univ : Set (ι → ℝ)), LowerSemicontinuousOn (fun z => f z lam) K := by
    intro lam _
    apply LowerSemicontinuous.lowerSemicontinuousOn
    apply LowerSemicontinuous.add' (neg_lsc _ hHusc)
      (continuous_coe_real_ereal.comp (hr_cont_z lam)).lowerSemicontinuous
    intro z
    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  -- upper semicontinuity in `lam`
  have hfx : ∀ z ∈ K, UpperSemicontinuousOn (fun lam => f z lam) Set.univ := by
    intro z _
    apply UpperSemicontinuous.upperSemicontinuousOn
    apply UpperSemicontinuous.add' upperSemicontinuous_const
      (continuous_coe_real_ereal.comp (hr_cont_l z)).upperSemicontinuous
    intro lam
    exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  -- quasiconcavity in `lam`
  have hfx' : ∀ z ∈ K, QuasiconcaveOn ℝ Set.univ (fun lam => f z lam) := by
    intro z _
    rw [quasiconcaveOn_iff_min_le]
    refine ⟨convex_univ, ?_⟩
    intro l₁ _ l₂ _ a b ha hb hab
    have hrm : min (r z l₁) (r z l₂) ≤ r z (a • l₁ + b • l₂) := by
      have e1 : ∑ i, (a • l₁ + b • l₂) i * mf D c i z =
          a * ∑ i, l₁ i * mf D c i z + b * ∑ i, l₂ i * mf D c i z := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      have e2 : ∑ i, |(a • l₁ + b • l₂) i| ≤ a * ∑ i, |l₁ i| + b * ∑ i, |l₂ i| := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum; intro i _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc |a * l₁ i + b * l₂ i| ≤ |a * l₁ i| + |b * l₂ i| := abs_add_le _ _
          _ = a * |l₁ i| + b * |l₂ i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      have e3 : r z (a • l₁ + b • l₂) ≥ a * r z l₁ + b * r z l₂ := by
        simp only [hr]
        rw [e1]
        have := mul_le_mul_of_nonneg_left e2 hε
        nlinarith
      rcases le_total (r z l₁) (r z l₂) with hle | hle
      · rw [min_eq_left hle]
        have h1 := mul_le_mul_of_nonneg_left hle hb
        have e : a * r z l₁ + b * r z l₁ = r z l₁ := by rw [← add_mul, hab, one_mul]
        linarith
      · rw [min_eq_right hle]
        have h1 := mul_le_mul_of_nonneg_left hle ha
        have e : a * r z l₂ + b * r z l₂ = r z l₂ := by rw [← add_mul, hab, one_mul]
        linarith
    rcases min_le_iff.mp hrm with h1 | h1
    · exact (min_le_left _ _).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr h1))
    · exact (min_le_right _ _).trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr h1))
  -- quasiconvexity in `z`
  have hfy' : ∀ lam ∈ (Set.univ : Set (ι → ℝ)), QuasiconvexOn ℝ K (fun z => f z lam) := by
    intro lam _
    rw [quasiconvexOn_iff_le_max]
    refine ⟨hKconv, ?_⟩
    intro z₁ hz₁ z₂ hz₂ a b ha hb hab
    by_cases t₁ : f z₁ lam = ⊤
    · rw [t₁]; exact le_max_of_le_left le_top
    by_cases t₂ : f z₂ lam = ⊤
    · rw [t₂]; exact le_max_of_le_right le_top
    have hH₁ : Hf D h z₁ ≠ ⊥ := by
      intro hb'; apply t₁; simp only [hf, hb', EReal.neg_bot, EReal.top_add_coe]
    have hH₂ : Hf D h z₂ ≠ ⊥ := by
      intro hb'; apply t₂; simp only [hf, hb', EReal.neg_bot, EReal.top_add_coe]
    have nb₁ := H_nb_of_ne_bot z₁ hH₁
    have nb₂ := H_nb_of_ne_bot z₂ hH₂
    set s₁ := ∑ x, ∑ y, D x y * (h y (z₁ x y)).toReal with hs₁
    set s₂ := ∑ x, ∑ y, D x y * (h y (z₂ x y)).toReal with hs₂
    have eH₁ : Hf D h z₁ = (s₁ : EReal) := H_real hD0 htop z₁ nb₁
    have eH₂ : Hf D h z₂ = (s₂ : EReal) := H_real hD0 htop z₂ nb₂
    have hw : ((a * s₁ + b * s₂ : ℝ) : EReal) ≤ Hf D h (a • z₁ + b • z₂) := by
      have := le_H hD0 (a • z₁ + b • z₂)
        (fun x y => a * (h y (z₁ x y)).toReal + b * (h y (z₂ x y)).toReal) (by
          intro x y hpos
          exact h_concave (hgh y) (z₁ x y) (z₂ x y) _ _ a b
            (EReal.coe_toReal (htop _ _) (nb₁ x y hpos)).symm
            (EReal.coe_toReal (htop _ _) (nb₂ x y hpos)).symm ha hb hab)
      convert this using 2
      simp only [hs₁, hs₂, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
      congr 1 <;> (apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; ring)
    have hrw : r (a • z₁ + b • z₂) lam = a * r z₁ lam + b * r z₂ lam := by
      simp only [hr, m_affine _ z₁ z₂ a b hab]
      have e1 : ∑ i, lam i * (a * mf D c i z₁ + b * mf D c i z₂) =
          a * ∑ i, lam i * mf D c i z₁ + b * ∑ i, lam i * mf D c i z₂ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [e1]
      linear_combination (ε * ∑ i, |lam i|) * hab
    have ef₁ : f z₁ lam = ((-s₁ + r z₁ lam : ℝ) : EReal) := by
      simp only [hf, eH₁]; norm_cast
    have ef₂ : f z₂ lam = ((-s₂ + r z₂ lam : ℝ) : EReal) := by
      simp only [hf, eH₂]; norm_cast
    have hfw : f (a • z₁ + b • z₂) lam ≤
        ((a * (-s₁ + r z₁ lam) + b * (-s₂ + r z₂ lam) : ℝ) : EReal) := by
      have h1 : f (a • z₁ + b • z₂) lam ≤
          -((a * s₁ + b * s₂ : ℝ) : EReal) + ((r (a • z₁ + b • z₂) lam : ℝ) : EReal) :=
        add_le_add (EReal.neg_le_neg_iff.mpr hw) le_rfl
      refine h1.trans (le_of_eq ?_)
      rw [hrw, ← EReal.coe_neg, ← EReal.coe_add]
      congr 1; ring
    rw [ef₁, ef₂]
    refine hfw.trans ?_
    rcases le_total (-s₁ + r z₁ lam) (-s₂ + r z₂ lam) with hle | hle
    · refine le_max_of_le_right (EReal.coe_le_coe_iff.mpr ?_)
      have h1 := mul_le_mul_of_nonneg_left hle ha
      have e : a * (-s₂ + r z₂ lam) + b * (-s₂ + r z₂ lam) = -s₂ + r z₂ lam := by
        rw [← add_mul, hab, one_mul]
      linarith
    · refine le_max_of_le_left (EReal.coe_le_coe_iff.mpr ?_)
      have h1 := mul_le_mul_of_nonneg_left hle hb
      have e : a * (-s₁ + r z₁ lam) + b * (-s₁ + r z₁ lam) = -s₁ + r z₁ lam := by
        rw [← add_mul, hab, one_mul]
      linarith
  -- Sion's minimax theorem
  have hS := Sion.minimax' (β := EReal) (X := K) (Y := (Set.univ : Set (ι → ℝ))) (f := f)
    ⟨z₀, hz₀K⟩ hKconv hKc hfy hfy' convex_univ hfx hfx'
  -- infeasible points have supremum `⊤`
  have hinf : ∀ z ∈ K, z ∉ Sf → ⨆ lam ∈ (Set.univ : Set (ι → ℝ)), f z lam = ⊤ := by
    intro z hzK hzS
    have : ¬ ∀ i, |mf D c i z| ≤ ε := fun h' => hzS ⟨hzK, h'⟩
    push Not at this
    obtain ⟨i, hi⟩ := this
    by_cases hHb : Hf D h z = ⊥
    · apply top_unique
      refine le_iSup₂_of_le (0 : ι → ℝ) (Set.mem_univ _) (le_of_eq ?_)
      simp only [hf, hHb, EReal.neg_bot, EReal.top_add_coe]
    · set s := (Hf D h z).toReal with hs
      have eH : Hf D h z = (s : EReal) := (EReal.coe_toReal (H_ne_top hD0 htop z) hHb).symm
      rw [EReal.eq_top_iff_forall_lt]
      intro M
      set m := mf D c i z with hm
      have hmpos : 0 < |m| - ε := by linarith
      have hm0 : 0 < |m| := by linarith
      set t : ℝ := (|M| + |s| + 1) / (|m| * (|m| - ε)) with ht
      have htpos : 0 < t := div_pos (by positivity) (mul_pos hm0 hmpos)
      set lam : ι → ℝ := Pi.single i (t * m) with hlam
      have e1 : ∑ j, lam j * mf D c j z = t * m * m := by
        rw [Finset.sum_eq_single i]
        · simp [hlam, hm]
        · intro j _ hj; simp [hlam, Pi.single_apply, hj]
        · intro h'; exact absurd (Finset.mem_univ i) h'
      have e2 : ∑ j, |lam j| = t * |m| := by
        rw [Finset.sum_eq_single i]
        · simp [hlam, abs_mul, abs_of_pos htpos]
        · intro j _ hj; simp [hlam, Pi.single_apply, hj]
        · intro h'; exact absurd (Finset.mem_univ i) h'
      have hrval : r z lam = |M| + |s| + 1 := by
        simp only [hr]
        rw [e1, e2]
        have : m * m = |m| * |m| := by rw [← abs_mul_abs_self m]
        rw [ht]
        field_simp
        nlinarith [this]
      refine lt_of_lt_of_le ?_ (le_iSup₂_of_le lam (Set.mem_univ _) le_rfl)
      simp only [hf, eH, hrval]
      rw [← EReal.coe_neg, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      have := le_abs_self M
      have := le_abs_self s
      linarith
  -- approximate attainment of the inner supremum
  have happrox : ∀ lam : ι → ℝ, ∀ δ : ℝ, 0 < δ →
      ∃ z ∈ K, f z lam ≤ ((-L lam + δ : ℝ) : EReal) := by
    intro lam δ hδ
    choose b hbS hb using fun (x : X) (y : Fin k) =>
      h_approx (hgh y) (hdom y) (centered (combo c lam x)) δ hδ
    have hbK : b ∈ K := fun x y => hbS x y
    refine ⟨b, hbK, ?_⟩
    have hlow := le_H hD0 b (fun x y => g y (centered (combo c lam x)) - δ +
      centered (combo c lam x) ⬝ᵥ b x y) (fun x y _ => (hb x y).le)
    have hsum : ∑ x, ∑ y, D x y * (g y (centered (combo c lam x)) - δ +
        centered (combo c lam x) ⬝ᵥ b x y) =
        (∑ x, ∑ y, D x y * g y (centered (combo c lam x))) - δ + ∑ i, lam i * mf D c i b := by
      rw [← hkey b hbK lam]
      have hD1 : ∑ x, ∑ y, D x y * δ = δ := by simp_rw [← Finset.sum_mul, hD.2, one_mul]
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hD1]
    rw [hsum] at hlow
    have h1 : f b lam ≤ -(((∑ x, ∑ y, D x y * g y (centered (combo c lam x))) - δ +
        ∑ i, lam i * mf D c i b : ℝ) : EReal) + ((r b lam : ℝ) : EReal) :=
      add_le_add (EReal.neg_le_neg_iff.mpr hlow) le_rfl
    refine h1.trans (le_of_eq ?_)
    rw [← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    simp only [hr, hL, lossObjective]
    ring
  have hR_each : ∀ lam : ι → ℝ, ⨅ z ∈ K, f z lam ≤ -((L lam : ℝ) : EReal) := by
    intro lam
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    rw [← EReal.coe_neg, EReal.coe_lt_coe_iff] at hq1
    obtain ⟨z, hzK, hz⟩ := happrox lam (q + L lam) (by linarith)
    have h1 : ⨅ z ∈ K, f z lam ≤ f z lam := iInf₂_le z hzK
    have h2 : ((-L lam + (q + L lam) : ℝ) : EReal) = (q : EReal) := by congr 1; ring
    rw [h2] at hz
    exact absurd (hq2.trans_le (h1.trans hz)) (lt_irrefl _)
  -- assembling the minimax inequality
  have hLHS : -Hf D h zs ≤ ⨅ z ∈ K, ⨆ lam ∈ (Set.univ : Set (ι → ℝ)), f z lam := by
    apply le_iInf₂; intro z hzK
    by_cases hzS : z ∈ Sf
    · have h1 : f z 0 = -Hf D h z := by simp [hf, hr]
      calc -Hf D h zs ≤ -Hf D h z := EReal.neg_le_neg_iff.mpr (hzsmax hzS)
        _ = f z 0 := h1.symm
        _ ≤ ⨆ lam ∈ (Set.univ : Set (ι → ℝ)), f z lam := le_iSup₂_of_le 0 (Set.mem_univ _) le_rfl
    · rw [hinf z hzK hzS]; exact le_top
  have hRHS : ⨆ lam ∈ (Set.univ : Set (ι → ℝ)), ⨅ z ∈ K, f z lam ≤ -V := by
    apply iSup₂_le; intro lam _
    exact (hR_each lam).trans (EReal.neg_le_neg_iff.mpr (iInf_le _ lam))
  have hVle : V ≤ Hf D h zs := by
    have := hLHS.trans (hS ▸ hRHS)
    exact EReal.neg_le_neg_iff.mp this
  have hge : ∀ z ∈ Sf, Hf D h z ≤ V := fun z hz => le_iInf (fun lam => hweak z hz lam)
  refine ⟨⟨zs, hzsS.1, hzsS.2, le_antisymm hVle (hge zs hzsS)⟩, ?_⟩
  rintro v ⟨z, hz1, hz2, rfl⟩
  exact hge z ⟨hz1, hz2⟩
