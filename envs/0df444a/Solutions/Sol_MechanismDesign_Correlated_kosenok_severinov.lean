-- Prove2me | solution 1 for MechanismDesign.Correlated.kosenok_severinov
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T08:20:20.939618+00:00
-- url     : https://prove2.me/submissions/0ce54261-87cc-4326-b9c3-c8028da4d5de

import Mathlib
import Definitions.Def_MechanismDesign_Correlated_FiniteModel



namespace MechanismDesign.Correlated

open FiniteTypes
open scoped Pointwise

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)]

lemma cm_sum_fib (i : ι) (x y : Θ i) (G : (∀ j, Θ j) → ℝ)
    (hG : ∀ θ a, G (Function.update θ i a) = G θ) :
    ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), G θ =
      ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y), G θ := by
  apply Finset.sum_nbij' (fun θ => Function.update θ i y) (fun θ => Function.update θ i x)
  · intro θ _; simp
  · intro θ _; simp
  · intro θ hθ
    have hθ' : θ i = x := by simpa using hθ
    simp only [Function.update_idem]
    rw [← hθ']; exact Function.update_eq_self i θ
  · intro θ hθ
    have hθ' : θ i = y := by simpa using hθ
    simp only [Function.update_idem]
    rw [← hθ']; exact Function.update_eq_self i θ
  · intro θ _; rw [hG]

lemma cm_condProb_inv (μ : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (θ : ∀ j, Θ j) (a : Θ i) :
    condProb μ i x (Function.update θ i a) = condProb μ i x θ := by
  simp [condProb]

lemma cm_condExp_congr (μ : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (g g' : (∀ j, Θ j) → ℝ)
    (h : ∀ θ, θ i = x → g θ = g' θ) : condExp μ i x g = condExp μ i x g' := by
  unfold condExp
  apply Finset.sum_congr rfl
  intro θ hθ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  rw [h θ hθ]

lemma cm_condExp_lin (μ : (∀ i, Θ i) → ℝ) (i : ι) (x : Θ i) (a b : (∀ j, Θ j) → ℝ) (c : ℝ) :
    condExp μ i x (fun θ => a θ - c * b θ) = condExp μ i x a - c * condExp μ i x b := by
  unfold condExp
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro θ _; ring

lemma cm_condExp_inv (μ : (∀ i, Θ i) → ℝ) (i : ι) (x y : Θ i) (G : (∀ j, Θ j) → ℝ)
    (hG : ∀ θ a, G (Function.update θ i a) = G θ) :
    condExp μ i x G =
      ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y), G θ * condProb μ i x θ := by
  unfold condExp
  apply cm_sum_fib
  intro θ a
  rw [hG, cm_condProb_inv]

lemma cm_condExp_one (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (i : ι) (x : Θ i) :
    condExp μ i x (fun _ => 1) = 1 := by
  obtain ⟨θs, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ)
    (by rw [hμ.2]; norm_num)
  have hpos : 0 < typeProb μ i x := by
    unfold typeProb
    exact Finset.sum_pos' (fun θ _ => (hμ.1 θ).le)
      ⟨Function.update θs i x, by simp, hμ.1 _⟩
  unfold condExp condProb
  have : ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x),
      (1 : ℝ) * (μ (Function.update θ i x) / typeProb μ i x) =
      ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = x), μ θ / typeProb μ i x := by
    apply Finset.sum_congr rfl
    intro θ hθ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
    rw [← hθ, Function.update_eq_self, one_mul]
  rw [this, ← Finset.sum_div]
  exact div_self hpos.ne'


lemma ks_sig {i : ι} {p q : Θ i × Θ i} (h : (⟨i, p⟩ : Σ i, Θ i × Θ i) = ⟨i, q⟩) : p = q :=
  eq_of_heq (Sigma.mk.inj_iff.1 h).2

lemma ks_rep {R : Type*} [Fintype R] [DecidableEq R] (f : (R → ℝ) →L[ℝ] ℝ) (v : R → ℝ) :
    f v = ∑ r, v r * f (fun r' => if r = r' then 1 else 0) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro θ _
  rw [map_smul, smul_eq_mul]

lemma ks_nonempty (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) : Nonempty (∀ i, Θ i) := by
  obtain ⟨θs, -, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ)
    (by rw [hμ.2]; norm_num)
  exact ⟨θs⟩

lemma ks_typeProb_pos (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (i : ι) (x : Θ i) :
    0 < typeProb μ i x := by
  obtain ⟨θs⟩ := ks_nonempty μ hμ
  unfold typeProb
  exact Finset.sum_pos' (fun θ _ => (hμ.1 θ).le) ⟨Function.update θs i x, by simp, hμ.1 _⟩

lemma ks_fib_one (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (i : ι) (x y : Θ i) :
    ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i = y), condProb μ i x θ = 1 := by
  rw [← cm_condExp_one μ hμ i x, cm_condExp_inv μ i x y (fun _ => 1) (fun _ _ => rfl)]
  simp

lemma ks_mu_eq (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (i : ι) (x : Θ i)
    (θ : ∀ j, Θ j) : μ (Function.update θ i x) = typeProb μ i x * condProb μ i x θ := by
  unfold condProb
  field_simp [(ks_typeProb_pos μ hμ i x).ne']

lemma ks_const (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ) (r : (∀ i, Θ i) → ℝ)
    (H : ∀ i (θ1 θ2 : ∀ j, Θ j), θ1 i = θ2 i → r θ1 = r θ2) (θ θ' : ∀ j, Θ j) : r θ = r θ' := by
  by_cases hij : ∃ i j : ι, i ≠ j
  · obtain ⟨i, j, hij⟩ := hij
    let θ'' : ∀ k, Θ k := Function.update θ' i (θ i)
    rw [H i θ θ'' (by simp [θ''])]
    exact H j θ'' θ' (by simp [θ'', Function.update_of_ne hij.symm])
  · push_neg at hij
    by_cases hθ : θ = θ'
    · rw [hθ]
    · exfalso
      obtain ⟨i, hi⟩ : ∃ i, θ i ≠ θ' i := by
        by_contra h; push_neg at h; exact hθ (funext h)
      have hone : ∀ (x : Θ i) (θ0 : ∀ j, Θ j), condProb μ i x θ0 = 1 := by
        intro x θ0
        have hfib : ∀ θ1 : ∀ j, Θ j, θ1 i = x → θ1 = Function.update θ0 i x := by
          intro θ1 h1
          funext k
          have := hij k i
          subst this
          simp [h1]
        unfold condProb typeProb
        rw [Finset.sum_eq_single (Function.update θ0 i x)]
        · exact div_self (hμ.1 _).ne'
        · intro b hb hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
          exact absurd (hfib b hb) hne
        · intro h; simp at h
      apply hCM
      refine ⟨i, θ i, Pi.single (θ' i) 1, fun y _ => ?_, fun θ0 => ?_⟩
      · simp only [Pi.single_apply]; split_ifs <;> norm_num
      · rw [Finset.sum_eq_single (θ' i)]
        · simp [hone]
        · intro b _ hb; simp [Pi.single_apply, hb]
        · intro h; exact absurd (Finset.mem_erase.2 ⟨hi.symm, Finset.mem_univ _⟩) h

lemma ks_budget (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (s : (∀ i, Θ i) → ℝ) (hs : ∑ θ, μ θ * s θ = 0) :
    ∃ z : ι → (∀ i, Θ i) → ℝ, (∀ i x, condExp μ i x (z i) = 0) ∧ ∀ θ, ∑ i, z i θ = s θ := by
  classical
  let IntMap : (ι × (∀ i, Θ i) → ℝ) →ₗ[ℝ] (∀ i, Θ i → ℝ) :=
    { toFun := fun e i x => condExp μ i x (fun θ => e (i, θ))
      map_add' := by
        intro a b; funext i x
        simp only [condExp, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a; funext i x
        simp only [condExp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  let Bud : (ι × (∀ i, Θ i) → ℝ) →ₗ[ℝ] ((∀ i, Θ i) → ℝ) :=
    { toFun := fun e θ => ∑ i, e (i, θ)
      map_add' := by intro a b; funext θ; simp [Finset.sum_add_distrib]
      map_smul' := by intro c a; funext θ; simp [Finset.mul_sum] }
  let V := (LinearMap.ker IntMap).map Bud
  by_cases hsV : s ∈ V
  · obtain ⟨e, he, hes⟩ := Submodule.mem_map.1 hsV
    refine ⟨fun i θ => e (i, θ), fun i x => ?_, fun θ => ?_⟩
    · have := congrFun (congrFun (LinearMap.mem_ker.1 he) i) x
      exact this
    · exact congrFun hes θ
  exfalso
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed V.convex
    V.closed_of_finiteDimensional hsV
  have hu : u < 0 := by simpa using hb 0 V.zero_mem
  have hvan : ∀ b ∈ V, f b = 0 := by
    intro b hbV
    by_contra hne
    have := hb (((u - 1) / f b) • b) (V.smul_mem _ hbV)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  let g : (∀ i, Θ i) → ℝ := fun θ => f (fun θ' => if θ = θ' then 1 else 0)
  have hfg : ∀ v, f v = ∑ θ, v θ * g θ := fun v => ks_rep f v
  have hrel : ∀ i (θ1 θ2 : ∀ j, Θ j), θ1 i = θ2 i → g θ1 / μ θ1 = g θ2 / μ θ2 := by
    intro i θ1 θ2 h12
    let e : ι × (∀ i, Θ i) → ℝ := fun r =>
      (if r = (i, θ1) then μ θ2 else 0) - (if r = (i, θ2) then μ θ1 else 0)
    have heW : e ∈ LinearMap.ker IntMap := by
      rw [LinearMap.mem_ker]
      funext j x
      show condExp μ j x (fun θ => e (j, θ)) = 0
      by_cases hj : j = i
      · subst hj
        unfold condExp
        simp only [e, Prod.mk.injEq, true_and, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hx : θ1 j = x
        · have hx2 : θ2 j = x := h12 ▸ hx
          rw [if_pos hx, if_pos hx2]
          subst hx
          unfold condProb
          rw [Function.update_eq_self, ← hx2, Function.update_eq_self]
          ring
        · have hx2 : ¬ θ2 j = x := h12 ▸ hx
          rw [if_neg hx, if_neg hx2]; ring
      · unfold condExp
        apply Finset.sum_eq_zero
        intro θ _
        simp [e, hj]
    have := hvan _ (Submodule.mem_map_of_mem heW)
    rw [hfg] at this
    have hB : ∀ θ, Bud e θ = (if θ = θ1 then μ θ2 else 0) - (if θ = θ2 then μ θ1 else 0) := by
      intro θ
      show ∑ j, e (j, θ) = _
      rw [Finset.sum_eq_single i]
      · simp [e]
      · intro b _ hb; simp [e, hb]
      · intro h; simp at h
    simp only [hB, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at this
    have h1 := hμ.1 θ1
    have h2 := hμ.1 θ2
    rw [div_eq_div_iff h1.ne' h2.ne']
    linarith
  obtain ⟨θ0⟩ := ks_nonempty μ hμ
  have hc : ∀ θ, g θ = (g θ0 / μ θ0) * μ θ := by
    intro θ
    have := ks_const μ hμ hCM (fun θ => g θ / μ θ) hrel θ θ0
    rw [← this, div_mul_cancel₀ _ (hμ.1 θ).ne']
  have hfs : f s = 0 := by
    rw [hfg]
    have : ∑ θ, s θ * g θ = (g θ0 / μ θ0) * ∑ θ, μ θ * s θ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro θ _; rw [hc θ]; ring
    rw [this, hs, mul_zero]
  linarith

lemma ks_lie (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (hId : Identifiable μ) :
    ∃ w : ι → (∀ i, Θ i) → ℝ, (∀ i x, condExp μ i x (w i) = 0) ∧ (∀ θ, ∑ i, w i θ = 0) ∧
      ∀ i (x y : Θ i), x ≠ y → 0 < condExp μ i x (fun θ => w i (Function.update θ i y)) := by
  classical
  by_cases hK : ∃ k : (Σ i, Θ i × Θ i), k.2.1 ≠ k.2.2
  swap
  · push_neg at hK
    refine ⟨fun _ _ => 0, fun i x => by simp [condExp], fun θ => by simp, fun i x y hxy => ?_⟩
    exact absurd (hK ⟨i, (x, y)⟩) hxy
  obtain ⟨k0, hk0⟩ := hK
  let K0 := Σ i, Θ i × Θ i
  let Λset : Set (K0 → ℝ) := {l | (∀ k, 0 ≤ l k) ∧ ∑ k, l k = 1 ∧ ∀ k : K0, k.2.1 = k.2.2 → l k = 0}
  let Llie : (K0 → ℝ) →ₗ[ℝ] (ι × (∀ i, Θ i) → ℝ) :=
    { toFun := fun l r => ∑ x, l ⟨r.1, (x, r.2 r.1)⟩ * condProb μ r.1 x r.2
      map_add' := by intro a b; funext r; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; funext r; simp [Finset.mul_sum, mul_assoc] }
  let Lint : ((∀ i, Θ i → ℝ) × ((∀ i, Θ i) → ℝ)) →ₗ[ℝ] (ι × (∀ i, Θ i) → ℝ) :=
    { toFun := fun ab r => ab.1 r.1 (r.2 r.1) * condProb μ r.1 (r.2 r.1) r.2 + ab.2 r.2
      map_add' := by intro a b; funext r; simp; ring
      map_smul' := by intro c a; funext r; simp; ring }
  have hΛcl : IsClosed Λset := by
    have : Λset = (⋂ k, {l : K0 → ℝ | 0 ≤ l k}) ∩ {l | ∑ k, l k = 1} ∩
        ⋂ k : K0, {l | k.2.1 = k.2.2 → l k = 0} := by
      ext l; simp [Λset, and_assoc]
    rw [this]
    refine ((isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_eq (continuous_finset_sum _ fun k _ => continuous_apply k) continuous_const)).inter
      (isClosed_iInter fun k => ?_)
    by_cases h : k.2.1 = k.2.2
    · simp only [h, forall_const]; exact isClosed_eq (continuous_apply k) continuous_const
    · simp only [h, IsEmpty.forall_iff, Set.setOf_true]; exact isClosed_univ
  have hΛcpt : IsCompact Λset := by
    apply (isCompact_stdSimplex ℝ K0).of_isClosed_subset hΛcl
    intro l hl; exact ⟨hl.1, hl.2.1⟩
  have hΛconv : Convex ℝ Λset := by
    intro a ha b hb p q hp hq hpq
    refine ⟨fun k => ?_, ?_, fun k hk => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := ha.1 k; have := hb.1 k; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, ha.2.1, hb.2.1]; linarith
    · simp [ha.2.2 k hk, hb.2.2 k hk]
  let C : Set (ι × (∀ i, Θ i) → ℝ) := Llie '' Λset + (LinearMap.range Lint : Set (ι × (∀ i, Θ i) → ℝ))
  have hCconv : Convex ℝ C := (hΛconv.linear_image Llie).add (LinearMap.range Lint).convex
  have hCcl : IsClosed C :=
    IsClosed.add_left_of_isCompact (LinearMap.range Lint).closed_of_finiteDimensional
      (hΛcpt.image Llie.continuous_of_finiteDimensional)
  have hsing : ∀ k : K0, k.2.1 ≠ k.2.2 → (Pi.single k (1:ℝ)) ∈ Λset := by
    intro k hk
    refine ⟨fun k' => ?_, by simp, fun k' hk' => ?_⟩
    · simp only [Pi.single_apply]; split_ifs <;> norm_num
    · have : k' ≠ k := by rintro rfl; exact hk hk'
      simp [Pi.single_apply, this]
  by_cases h0 : (0 : (ι × (∀ i, Θ i) → ℝ)) ∈ C
  · exfalso
    obtain ⟨_, ⟨lam, hlam, rfl⟩, v, hv, hsum⟩ := Set.mem_add.1 h0
    obtain ⟨ab, rfl⟩ := LinearMap.mem_range.1 hv
    have hEq : ∀ j (θ : ∀ i, Θ i), ∑ x, lam ⟨j, (x, θ j)⟩ * condProb μ j x θ +
        (ab.1 j (θ j) * condProb μ j (θ j) θ + ab.2 θ) = 0 := by
      intro j θ
      have := congrFun hsum (j, θ)
      simpa [Llie, Lint] using this
    let α := ab.1
    let γ : (∀ i, Θ i) → ℝ := fun θ => -ab.2 θ
    have hγ : ∀ i θ, γ θ = α i (θ i) * condProb μ i (θ i) θ +
        ∑ x, lam ⟨i, (x, θ i)⟩ * condProb μ i x θ := by
      intro i θ; have := hEq i θ; simp only [γ, α]; linarith
    have hev1 : ∀ᶠ ε in nhds (0:ℝ), ∀ θ, 0 < μ θ + ε * γ θ :=
      Filter.eventually_all.2 fun θ => continuousAt_const.eventually_lt
        (by fun_prop : ContinuousAt (fun ε : ℝ => μ θ + ε * γ θ) 0) (by simpa using hμ.1 θ)
    have hev2 : ∀ᶠ ε in nhds (0:ℝ), ∀ i x, 0 < typeProb μ i x + ε * α i x :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun x =>
        continuousAt_const.eventually_lt
        (by fun_prop : ContinuousAt (fun ε : ℝ => typeProb μ i x + ε * α i x) 0)
        (by simpa using ks_typeProb_pos μ hμ i x)
    obtain ⟨ε, ⟨h1, h2⟩, hεpos⟩ := (((hev1.and hev2).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ε ∈ Set.Ioi 0)).exists
    have hε : 0 < ε := hεpos
    haveI := ks_nonempty μ hμ
    let Z := ∑ θ, (μ θ + ε * γ θ)
    have hZ : 0 < Z := Finset.sum_pos (fun θ _ => h1 θ) Finset.univ_nonempty
    let ν : (∀ i, Θ i) → ℝ := fun θ => (μ θ + ε * γ θ) / Z
    have hν : IsFullSupportDist ν :=
      ⟨fun θ => div_pos (h1 θ) hZ, by simp only [ν]; rw [← Finset.sum_div]; exact div_self hZ.ne'⟩
    by_cases hνμ : ν = μ
    · have hγμ : ∀ θ, γ θ = ((Z - 1) / ε) * μ θ := by
        intro θ
        have := congrFun hνμ θ
        simp only [ν] at this
        rw [div_eq_iff hZ.ne'] at this
        rw [div_mul_eq_mul_div, eq_div_iff hε.ne']
        linarith
      obtain ⟨k, hk⟩ : ∃ k, 0 < lam k := by
        by_contra h; push_neg at h
        have := Finset.sum_nonpos (fun k (_ : k ∈ Finset.univ) => h k)
        linarith [hlam.2.1]
      obtain ⟨i0, x0, y0⟩ := k
      let Λ := ∑ x, lam ⟨i0, (x, y0)⟩
      have hΛ : 0 < Λ := lt_of_lt_of_le hk
        (Finset.single_le_sum (f := fun x => lam ⟨i0, (x, y0)⟩) (fun x _ => hlam.1 _)
          (Finset.mem_univ x0))
      let κ := (Z - 1) / ε * typeProb μ i0 y0 - α i0 y0
      have hfib : ∀ θ : ∀ i, Θ i, θ i0 = y0 →
          κ * condProb μ i0 y0 θ = ∑ x, lam ⟨i0, (x, y0)⟩ * condProb μ i0 x θ := by
        intro θ hθ
        have e1 := hγ i0 θ
        rw [hγμ θ, hθ] at e1
        have e2 := ks_mu_eq μ hμ i0 y0 θ
        rw [Function.update_eq_self_iff.2 hθ.symm] at e2
        rw [e2] at e1
        simp only [κ]
        linear_combination e1
      have hκ : κ = Λ := by
        have e1 : ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i0 = y0),
            κ * condProb μ i0 y0 θ = κ := by
          rw [← Finset.mul_sum, ks_fib_one μ hμ i0 y0 y0, mul_one]
        have e2 : ∑ θ ∈ Finset.univ.filter (fun θ : ∀ j, Θ j => θ i0 = y0),
            ∑ x, lam ⟨i0, (x, y0)⟩ * condProb μ i0 x θ = Λ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.mul_sum, ks_fib_one μ hμ i0 x y0, mul_one]
        have e3 := Finset.sum_congr (s₁ := Finset.univ.filter (fun θ : ∀ j, Θ j => θ i0 = y0)) rfl
          (fun θ hθ => hfib θ (by simpa using hθ))
        linarith
      apply hCM
      refine ⟨i0, y0, fun x => lam ⟨i0, (x, y0)⟩ / Λ, fun x _ => div_nonneg (hlam.1 _) hΛ.le,
        fun θ => ?_⟩
      rw [Finset.sum_erase _ (by simp [hlam.2.2 ⟨i0, (y0, y0)⟩ rfl])]
      have e := hfib (Function.update θ i0 y0) (by simp)
      rw [hκ] at e
      simp only [cm_condProb_inv] at e
      have : ∑ x, lam ⟨i0, (x, y0)⟩ / Λ * condProb μ i0 x θ =
          (∑ x, lam ⟨i0, (x, y0)⟩ * condProb μ i0 x θ) / Λ := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro x _; ring
      rw [this, ← e]
      field_simp
    · obtain ⟨i, x, hix⟩ := hId ν hν hνμ
      have htp := ks_typeProb_pos ν hν i x
      let D := Z * typeProb ν i x
      have hD : 0 < D := mul_pos hZ htp
      let W : Θ i → ℝ := fun y =>
        ((if y = x then typeProb μ i x + ε * α i x else 0) + ε * lam ⟨i, (y, x)⟩) / D
      have hW : ∀ y, 0 ≤ W y := by
        intro y
        apply div_nonneg _ hD.le
        apply add_nonneg
        · split_ifs
          · exact (h2 i x).le
          · exact le_refl 0
        · exact mul_nonneg hε.le (hlam.1 _)
      obtain ⟨θ, hθ⟩ := hix W hW
      apply hθ
      have hg := hγ i (Function.update θ i x)
      simp only [Function.update_self, cm_condProb_inv] at hg
      have hm := ks_mu_eq μ hμ i x θ
      have hR : ∑ y, W y * condProb μ i y θ =
          ((typeProb μ i x + ε * α i x) * condProb μ i x θ +
            ε * ∑ y, lam ⟨i, (y, x)⟩ * condProb μ i y θ) / D := by
        have : ∀ y, W y * condProb μ i y θ =
            ((if y = x then (typeProb μ i x + ε * α i x) * condProb μ i x θ else 0) +
              ε * (lam ⟨i, (y, x)⟩ * condProb μ i y θ)) / D := by
          intro y
          simp only [W]
          split_ifs with hy
          · subst hy; ring
          · ring
        rw [Finset.sum_congr rfl (fun y _ => this y), ← Finset.sum_div, Finset.sum_add_distrib,
          Finset.sum_ite_eq', ← Finset.mul_sum]
        simp
      rw [hR]
      show ν (Function.update θ i x) / typeProb ν i x = _
      simp only [ν]
      rw [hm, hg, div_div]
      congr 1
      ring
  · obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed hCconv hCcl h0
    have hmemC : ∀ k : K0, k.2.1 ≠ k.2.2 → ∀ v ∈ LinearMap.range Lint,
        Llie (Pi.single k 1) + v ∈ C := by
      intro k hk v hv
      exact Set.add_mem_add ⟨_, hsing k hk, rfl⟩ hv
    have hvan : ∀ v ∈ LinearMap.range Lint, f v = 0 := by
      intro v hv
      by_contra hne
      have := hb _ (hmemC k0 hk0 (((u - 1 - f (Llie (Pi.single k0 1))) / f v) • v)
        ((LinearMap.range Lint).smul_mem _ hv))
      rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      linarith
    have hpos : ∀ k : K0, k.2.1 ≠ k.2.2 → 0 < f (Llie (Pi.single k 1)) := by
      intro k hk
      have := hb _ (hmemC k hk 0 (LinearMap.range Lint).zero_mem)
      rw [add_zero] at this
      simp at hfu
      linarith
    let φ : ι × (∀ i, Θ i) → ℝ := fun r => f (fun r' => if r = r' then 1 else 0)
    have hfφ : ∀ v : (ι × (∀ i, Θ i) → ℝ), f v = ∑ r, v r * φ r := fun v => ks_rep f v
    refine ⟨fun i θ => φ (i, θ), fun i x => ?_, fun θ => ?_, fun i x y hxy => ?_⟩
    · have := hvan _ ⟨(fun j z => if (⟨j, z⟩ : Σ j, Θ j) = ⟨i, x⟩ then 1 else 0, 0), rfl⟩
      rw [hfφ, Fintype.sum_prod_type, Finset.sum_eq_single i] at this
      · unfold condExp
        rw [Finset.sum_filter]
        refine Eq.trans ?_ this
        apply Finset.sum_congr rfl
        intro θ _
        simp only [Lint, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, add_zero,
          Sigma.mk.inj_iff, heq_eq_eq, true_and]
        split_ifs with h
        · subst h; ring
        · ring
      · intro j _ hj
        apply Finset.sum_eq_zero
        intro θ _
        simp [Lint, hj]
      · intro h; simp at h
    · have := hvan _ ⟨(0, fun θ' => if θ = θ' then 1 else 0), rfl⟩
      rw [hfφ, Fintype.sum_prod_type] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_eq_single θ]
      · simp [Lint]
      · intro b _ hb; simp [Lint, Ne.symm hb]
      · intro h; simp at h
    · have := hpos ⟨i, (x, y)⟩ hxy
      rw [hfφ, Fintype.sum_prod_type, Finset.sum_eq_single i] at this
      · rw [cm_condExp_inv μ i x y _ (fun θ a => by simp)]
        convert this using 1
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro θ _
        simp only [Llie, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_mul, Finset.sum_eq_single x]
        · split_ifs with h
          · subst h; simp [Function.update_eq_self]; ring
          · simp only [Pi.single_apply]
            rw [if_neg (fun he => h (congrArg Prod.snd (ks_sig he)))]; ring
        · intro b _ hb
          simp only [Pi.single_apply]
          rw [if_neg (fun he => hb (congrArg Prod.fst (ks_sig he)))]; ring
        · intro h; simp at h
      · intro j _ hj
        apply Finset.sum_eq_zero
        intro θ _
        simp only [Llie, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro z _
        simp only [Pi.single_apply]
        rw [if_neg (fun he => hj (congrArg Sigma.fst he))]; ring
      · intro h; simp at h

end

theorem ks_core {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (hId : Identifiable μ) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A)
    (hBB : IsExAnteBB μ M) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' ∧ IsExPostBB M' := by
  obtain ⟨z, hz0, hzs⟩ := ks_budget μ hμ hCM (fun θ => -∑ i, M.t i θ) (by
    have := hBB; unfold IsExAnteBB at this
    simp only [mul_neg, Finset.sum_neg_distrib, this, neg_zero])
  obtain ⟨w, hw0, hwbb, hwpos⟩ := ks_lie μ hμ hCM hId
  let t0 : ι → (∀ i, Θ i) → ℝ := fun i θ => M.t i θ + z i θ
  let d : ∀ i, Θ i → (∀ j, Θ j) → ℝ := fun i y θ => w i (Function.update θ i y)
  have hd0 : ∀ i x, condExp μ i x (d i x) = 0 := by
    intro i x
    rw [← hw0 i x]
    apply cm_condExp_congr; intro θ hθ; simp only [d]; rw [← hθ, Function.update_eq_self]
  have hdpos : ∀ i x y, x ≠ y → 0 < condExp μ i x (d i y) := fun i x y h => hwpos i x y h
  let B : ∀ i, Θ i → Θ i → ℝ := fun i x y =>
    condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x - t0 i (Function.update θ i y)) -
      condExp μ i x (fun θ => u i (M.q θ) x - t0 i θ)
  let K : ℝ := ∑ i, ∑ x, ∑ y, |B i x y| / |condExp μ i x (d i y)|
  refine ⟨⟨M.q, fun i θ => t0 i θ + K * w i θ⟩, rfl, ?_, ?_, ?_⟩
  · intro i x
    have e1 : condExp μ i x (fun θ => t0 i θ + K * w i θ) =
        condExp μ i x (fun θ => t0 i θ - (-K) * w i θ) := by
      apply cm_condExp_congr; intro θ _; ring
    have e2 : condExp μ i x (t0 i) = condExp μ i x (fun θ => M.t i θ - (-1) * z i θ) := by
      apply cm_condExp_congr; intro θ _; simp only [t0]; ring
    show _ = condExp μ i x (fun θ => t0 i θ + K * w i θ)
    rw [e1, cm_condExp_lin, e2, cm_condExp_lin, hz0, hw0]; ring
  · intro i x y
    show condExp μ i x (fun θ => u i (M.q θ) x - (t0 i θ + K * w i θ)) ≥
      condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x -
        (t0 i (Function.update θ i y) + K * w i (Function.update θ i y)))
    have h1 : condExp μ i x (fun θ => u i (M.q θ) x - (t0 i θ + K * w i θ)) =
        condExp μ i x (fun θ => (u i (M.q θ) x - t0 i θ) - K * d i x θ) := by
      apply cm_condExp_congr; intro θ hθ; simp only [d]; rw [← hθ, Function.update_eq_self]; ring
    have h2 : condExp μ i x (fun θ => u i (M.q (Function.update θ i y)) x -
        (t0 i (Function.update θ i y) + K * w i (Function.update θ i y))) =
        condExp μ i x (fun θ => (u i (M.q (Function.update θ i y)) x -
          t0 i (Function.update θ i y)) - K * d i y θ) := by
      apply cm_condExp_congr; intro θ _; simp only [d]; ring
    rw [h1, h2, cm_condExp_lin, cm_condExp_lin, hd0]
    by_cases hxy : x = y
    · subst hxy
      have : condExp μ i x (fun θ => u i (M.q (Function.update θ i x)) x -
          t0 i (Function.update θ i x)) = condExp μ i x (fun θ => u i (M.q θ) x - t0 i θ) := by
        apply cm_condExp_congr; intro θ hθ; rw [← hθ, Function.update_eq_self]
      rw [this, hd0]
    · have hg := hdpos i x y hxy
      have hK : |B i x y| / |condExp μ i x (d i y)| ≤ K := by
        have h3 : |B i x y| / |condExp μ i x (d i y)| ≤
            ∑ y', |B i x y'| / |condExp μ i x (d i y')| :=
          Finset.single_le_sum (f := fun y' => |B i x y'| / |condExp μ i x (d i y')|)
            (fun _ _ => by positivity) (Finset.mem_univ y)
        have h4 : ∑ y', |B i x y'| / |condExp μ i x (d i y')| ≤
            ∑ x', ∑ y', |B i x' y'| / |condExp μ i x' (d i y')| :=
          Finset.single_le_sum (f := fun x' => ∑ y', |B i x' y'| / |condExp μ i x' (d i y')|)
            (fun _ _ => by positivity) (Finset.mem_univ x)
        have h5 : ∑ x', ∑ y', |B i x' y'| / |condExp μ i x' (d i y')| ≤ K :=
          Finset.single_le_sum
            (f := fun i' => ∑ x', ∑ y', |B i' x' y'| / |condExp μ i' x' (d i' y')|)
            (fun _ _ => by positivity) (Finset.mem_univ i)
        linarith
      rw [abs_of_pos hg, div_le_iff₀ hg] at hK
      have := le_abs_self (B i x y)
      simp only [B] at this hK
      linarith
  · intro θ
    show ∑ i, (t0 i θ + K * w i θ) = 0
    simp only [t0, Finset.sum_add_distrib, ← Finset.mul_sum, hwbb, hzs]
    ring

end MechanismDesign.Correlated

open MechanismDesign.Correlated
open FiniteTypes

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {Θ : ι → Type*}
    [∀ i, Fintype (Θ i)] [∀ i, DecidableEq (Θ i)] {A : Type*}
    (μ : (∀ i, Θ i) → ℝ) (hμ : IsFullSupportDist μ) (hCM : CremerMcLean μ)
    (hId : Identifiable μ) (u : ∀ i, A → Θ i → ℝ) (M : DirectMechanism ι Θ A)
    (hBB : IsExAnteBB μ M) :
    ∃ M' : DirectMechanism ι Θ A, M'.q = M.q ∧
      (∀ i (θi : Θ i), condExp μ i θi (M.t i) = condExp μ i θi (M'.t i)) ∧
      IsBIC μ u M' ∧ IsExPostBB M' := by
  exact ks_core μ hμ hCM hId u M hBB
