-- Prove2me | solution 1 for LovaszSchrijver.NPlus.nplusIndex_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:51:13.285359+00:00
-- url     : https://prove2.me/submissions/376d611b-8bc0-4c31-afc1-9a109d1df599

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_Constraints



namespace LovaszSchrijver.NPlus

section csbsec


theorem csb_arith (m s t i : ℕ) (hm : m % 2 = 1) (hs : s < m) (ht : t < m) (hi : i < m)
    (hsi : s ≠ i) (hti : t ≠ i) (h : t = (s + 1) % m) :
    (if i < s then s else s + 1) % 2 ≠ (if i < t then t else t + 1) % 2 := by
  rcases Nat.lt_or_ge (s + 1) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    split_ifs <;> omega
  · have : s + 1 = m := by omega
    rw [this, Nat.mod_self] at h
    split_ifs <;> omega

theorem csb_two {V : Type} (G : SimpleGraph V) (S : Set V) (a b : V)
    (hS : ∀ w ∈ S, w = a ∨ w = b) : (G.induce S).Colorable 2 := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (fun w : S => if (w : V) = a then (0 : Fin 2) else 1) ?_⟩
  intro x y hxy
  have hne : (x : V) ≠ y := G.ne_of_adj hxy
  rcases hS x x.2 with hx | hx <;> rcases hS y y.2 with hy | hy
  · exact absurd (hx.trans hy.symm) hne
  · have : (y : V) ≠ a := fun h => hne (hx.trans h.symm)
    simp [hx, this]
  · have : (x : V) ≠ a := fun h => hne (h.trans hy.symm)
    simp [hy, this]
  · exact absurd (hx.trans hy.symm) hne

theorem csb_hole {V : Type} (G : SimpleGraph V) (C : Finset V) (hC : IsOddHole G C)
    (S : Set V) (hS : ∀ w ∈ S, w ∈ C) (v : V) (hv : v ∈ C) (hvS : v ∉ S) :
    (G.induce S).Colorable 2 := by
  classical
  obtain ⟨m, hodd, hm3, f, hf⟩ := hC
  have hm : m % 2 = 1 := Nat.odd_iff.mp hodd
  let i : Fin m := f.symm ⟨v, hv⟩
  let idx : S → Fin m := fun w => f.symm ⟨w, hS w w.2⟩
  let n : S → ℕ := fun w => if i.val < (idx w).val then (idx w).val else (idx w).val + 1
  refine ⟨SimpleGraph.Coloring.mk (fun w : S => if n w % 2 = 0 then (0 : Fin 2) else 1) ?_⟩
  intro x y hxy
  have hfx : ((f (idx x) : C) : V) = x := by simp [idx]
  have hfy : ((f (idx y) : C) : V) = y := by simp [idx]
  have hadj : G.Adj ((f (idx x) : C) : V) ((f (idx y) : C) : V) := by
    rw [hfx, hfy]; exact hxy
  have hxi : (idx x).val ≠ i.val := by
    intro h
    have : idx x = i := Fin.ext h
    apply hvS
    have : ((f (idx x) : C) : V) = v := by rw [this]; simp [i]
    rw [← this, hfx]; exact x.2
  have hyi : (idx y).val ≠ i.val := by
    intro h
    have : idx y = i := Fin.ext h
    apply hvS
    have : ((f (idx y) : C) : V) = v := by rw [this]; simp [i]
    rw [← this, hfy]; exact y.2
  have key : n x % 2 ≠ n y % 2 := by
    rcases (hf _ _).mp hadj with h | h
    · exact csb_arith m _ _ _ hm (idx x).2 (idx y).2 i.2 hxi hyi h
    · exact (csb_arith m _ _ _ hm (idx y).2 (idx x).2 i.2 hyi hxi h).symm
  intro heq
  apply key
  split_ifs at heq with h1 h2 h2 <;> first | omega | exact absurd heq (by decide)

theorem csb_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card → ∀ v, 0 < chi B v →
        (G.induce {w | 0 < contractCoeff G (chi B) v w}).Colorable 2) ∧
    (∀ C : Finset V, IsOddHole G C → ∀ v, 0 < chi C v →
        (G.induce {w | 0 < contractCoeff G (chi C) v w}).Colorable 2) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ → ∀ v, 0 < wheelCoeff U u₀ v →
        (G.induce {w | 0 < contractCoeff G (wheelCoeff U u₀) v w}).Colorable 2) ∧
    (∀ D : Finset V, IsOddAntihole G D → ∀ v, 0 < chi D v →
        (G.induce {w | 0 < contractCoeff G (chi D) v w}).Colorable 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB _ v hv
    have hvB : v ∈ B := by by_contra h; simp [chi, h] at hv
    apply csb_two G _ v v
    intro w hw
    simp only [Set.mem_setOf_eq, contractCoeff, chi] at hw
    split_ifs at hw with h1 h2
    · exact absurd hw (lt_irrefl _)
    · exfalso; apply h1; right
      by_cases hwv : w = v
      · exact absurd (Or.inl hwv) h1
      · exact hB hvB h2 (Ne.symm hwv)
    · exact absurd hw (lt_irrefl _)
  · intro C hC v hv
    have hvC : v ∈ C := by by_contra h; simp [chi, h] at hv
    apply csb_hole G C hC _ _ v hvC
    · simp [contractCoeff]
    · intro w hw
      simp only [Set.mem_setOf_eq, contractCoeff, chi] at hw
      split_ifs at hw with h1 h2
      · exact absurd hw (lt_irrefl _)
      · exact h2
      · exact absurd hw (lt_irrefl _)
  · intro U u₀ hW v hv
    obtain ⟨hu₀, hC, hadj⟩ := hW
    by_cases hvu : v = u₀
    · subst hvu
      apply csb_two G _ v v
      intro w hw
      simp only [Set.mem_setOf_eq, contractCoeff, wheelCoeff] at hw
      split_ifs at hw with h1 h2 h3
      · exact absurd hw (lt_irrefl _)
      · exact absurd (Or.inl h2) h1
      · exact absurd (Or.inr (hadj w (Finset.mem_erase.mpr ⟨h2, h3⟩))) h1
      · exact absurd hw (lt_irrefl _)
    · have hvU : v ∈ U := by
        by_contra h; simp [wheelCoeff, hvu, h] at hv
      apply csb_hole G _ hC _ _ v (Finset.mem_erase.mpr ⟨hvu, hvU⟩)
      · simp [contractCoeff]
      · intro w hw
        simp only [Set.mem_setOf_eq, contractCoeff, wheelCoeff] at hw
        split_ifs at hw with h1 h2 h3
        · exact absurd hw (lt_irrefl _)
        · exfalso; apply h1; right; rw [h2]; exact (hadj v (Finset.mem_erase.mpr ⟨hvu, hvU⟩)).symm
        · exact Finset.mem_erase.mpr ⟨h2, h3⟩
        · exact absurd hw (lt_irrefl _)
  · intro D hD v hv
    have hvD : v ∈ D := by by_contra h; simp [chi, h] at hv
    obtain ⟨hD5, m, hodd, hm3, f, hf⟩ := hD
    have hm : m % 2 = 1 := Nat.odd_iff.mp hodd
    have hmcard : m = D.card := by
      have := Fintype.card_congr f; simpa using this
    let i : Fin m := f.symm ⟨v, hvD⟩
    have hi1 : (i.val + 1) % m < m := Nat.mod_lt _ (by omega)
    have hi2 : (i.val + (m - 1)) % m < m := Nat.mod_lt _ (by omega)
    apply csb_two G _ (f ⟨_, hi1⟩ : V) (f ⟨_, hi2⟩ : V)
    intro w hw
    simp only [Set.mem_setOf_eq, contractCoeff, chi] at hw
    split_ifs at hw with h1 h2
    · exact absurd hw (lt_irrefl _)
    · push_neg at h1
      let s : Fin m := f.symm ⟨w, h2⟩
      have hfs : ((f s : D) : V) = w := by simp [s]
      have hfi : ((f i : D) : V) = v := by simp [i]
      have hcadj : Gᶜ.Adj ((f i : D) : V) ((f s : D) : V) := by
        rw [hfs, hfi]
        rw [SimpleGraph.compl_adj]
        exact ⟨fun h => h1.1 h.symm, h1.2⟩
      rcases (hf _ _).mp hcadj with h | h
      · left; rw [← hfs]; congr 2; exact Fin.ext h
      · right; rw [← hfs]; congr 2; apply Fin.ext
        show s.val = (i.val + (m - 1)) % m
        have hs := s.2
        have hi := i.2
        rcases Nat.lt_or_ge (s.val + 1) m with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at h
          rw [h]
          rw [show s.val + 1 + (m - 1) = s.val + m by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt hs]
        · have : s.val + 1 = m := by omega
          rw [this, Nat.mod_self] at h
          rw [h, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    · exact absurd hw (lt_irrefl _)


end csbsec

section fracsec


open MeasureTheory Set

theorem vfb_intL (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∫ θ in Ioc (0:ℝ) 1, (Iio x).indicator (1 : ℝ → ℝ) θ = x := by
  rw [integral_indicator_one measurableSet_Iio]
  rw [measureReal_restrict_apply measurableSet_Iio]
  have : Iio x ∩ Ioc (0:ℝ) 1 = Ioo 0 x := by
    ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]; constructor
    · intro h; exact ⟨h.2.1, h.1⟩
    · intro h; exact ⟨h.2, h.1, by linarith [h.2]⟩
  rw [this, Real.volume_real_Ioo_of_le h0]; ring

theorem vfb_intR (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∫ θ in Ioc (0:ℝ) 1, (Ioi (1 - x)).indicator (1 : ℝ → ℝ) θ = x := by
  rw [integral_indicator_one measurableSet_Ioi]
  rw [measureReal_restrict_apply measurableSet_Ioi]
  have : Ioi (1 - x) ∩ Ioc (0:ℝ) 1 = Ioc (1 - x) 1 := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
    · intro h; exact ⟨h.1, h.2.2⟩
    · intro h; exact ⟨h.1, by linarith [h.1], h.2⟩
  rw [this, Real.volume_real_Ioc_of_le (by linarith)]; ring

theorem vfb_integ (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ) :
    IntegrableOn (fun θ => a * s.indicator (1 : ℝ → ℝ) θ) (Ioc 0 1) := by
  apply Integrable.const_mul
  apply IntegrableOn.indicator _ hs
  exact integrableOn_const (by simp)

theorem vfb_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b : ℝ)
    (hvalid : Valid (STAB G) a b) (hbip : (G.induce {i | a i ≠ 0}).Colorable 2) :
    Valid (FRAC G) a b := by
  classical
  intro x hx
  obtain ⟨hx0, hxe⟩ := hx
  have hx1 : ∀ i, x i ≤ 1 := by
    intro i
    obtain ⟨j, hj⟩ := hG i
    linarith [hxe i j hj, hx0 j]
  obtain ⟨c⟩ := hbip
  let L : V → Prop := fun i => ∃ h : a i ≠ 0, c ⟨i, h⟩ = 0
  let I : ℝ → Finset V := fun θ => Finset.univ.filter
    (fun i => 0 < a i ∧ ((L i ∧ θ < x i) ∨ (¬ L i ∧ 1 - x i < θ)))
  -- each level set is stable
  have hstab : ∀ θ, ∑ i, a i * chi (I θ) i ≤ b := by
    intro θ
    apply hvalid
    apply subset_convexHull
    refine ⟨I θ, ?_, rfl⟩
    intro i hi j hj hij hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq, I] at hi hj
    have hai : a i ≠ 0 := ne_of_gt hi.1
    have haj : a j ≠ 0 := ne_of_gt hj.1
    have hcv : c ⟨i, hai⟩ ≠ c ⟨j, haj⟩ := c.valid (by simpa using hadj)
    rcases hi.2 with ⟨hLi, hθi⟩ | ⟨hLi, hθi⟩ <;> rcases hj.2 with ⟨hLj, hθj⟩ | ⟨hLj, hθj⟩
    · obtain ⟨_, h1⟩ := hLi; obtain ⟨_, h2⟩ := hLj
      exact hcv (h1.trans h2.symm)
    · linarith [hxe i j hadj]
    · linarith [hxe i j hadj]
    · have h1 : c ⟨i, hai⟩ ≠ 0 := fun h => hLi ⟨hai, h⟩
      have h2 : c ⟨j, haj⟩ ≠ 0 := fun h => hLj ⟨haj, h⟩
      apply hcv
      revert h1 h2
      generalize c ⟨i, hai⟩ = p; generalize c ⟨j, haj⟩ = q
      intro h1 h2; fin_cases p <;> fin_cases q <;> simp_all
  -- rewrite each summand as an indicator
  let g : V → ℝ → ℝ := fun i θ => if 0 < a i then
      (if L i then a i * (Iio (x i)).indicator (1 : ℝ → ℝ) θ
        else a i * (Ioi (1 - x i)).indicator (1 : ℝ → ℝ) θ) else 0
  have hg : ∀ i θ, a i * chi (I θ) i = g i θ := by
    intro i θ
    simp only [g, chi, I, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : 0 < a i
    · by_cases hL : L i
      · by_cases ht : θ < x i
        · simp [ha, hL, ht, indicator_of_mem (show θ ∈ Iio (x i) from ht)]
        · simp [ha, hL, ht, indicator_of_notMem (show θ ∉ Iio (x i) from ht)]
      · by_cases ht : 1 - x i < θ
        · simp [ha, hL, ht, indicator_of_mem (show θ ∈ Ioi (1 - x i) from ht)]
        · simp [ha, hL, ht, indicator_of_notMem (show θ ∉ Ioi (1 - x i) from ht)]
    · simp [ha]
  have hgint : ∀ i, IntegrableOn (g i) (Ioc 0 1) := by
    intro i
    simp only [g]
    split_ifs
    · exact vfb_integ _ measurableSet_Iio _
    · exact vfb_integ _ measurableSet_Ioi _
    · exact integrableOn_const (by simp)
  have hgval : ∀ i, ∫ θ in Ioc (0:ℝ) 1, g i θ = if 0 < a i then a i * x i else 0 := by
    intro i
    simp only [g]
    split_ifs
    · rw [integral_const_mul, vfb_intL _ (hx0 i) (hx1 i)]
    · rw [integral_const_mul, vfb_intR _ (hx0 i) (hx1 i)]
    · simp
  have hmono : ∫ θ in Ioc (0:ℝ) 1, (∑ i, g i θ) ≤ ∫ θ in Ioc (0:ℝ) 1, b := by
    apply setIntegral_mono
    · exact integrable_finset_sum _ (fun i _ => hgint i)
    · exact integrableOn_const (by simp)
    · intro θ
      have := hstab θ
      simp only [hg] at this
      exact this
  rw [integral_finset_sum _ (fun i _ => hgint i)] at hmono
  simp only [hgval, setIntegral_const] at hmono
  have hvol : (volume (Ioc (0:ℝ) 1)).toReal = 1 := by simp
  have : volume.real (Ioc (0:ℝ) 1) = 1 := by simp
  rw [this, one_smul] at hmono
  calc ∑ i, a i * x i ≤ ∑ i, (if 0 < a i then a i * x i else 0) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with h
        · exact le_rfl
        · push_neg at h; exact mul_nonpos_of_nonpos_of_nonneg h (hx0 i)
    _ ≤ b := hmono


end fracsec

section lssec


open Matrix

theorem ls_Qnonneg {ι : Type} (q : Option ι → ℝ) (hq : q ∈ (Q : Set (Option ι → ℝ)))
    (j : Option ι) : 0 ≤ q j := by
  unfold Q cone at hq
  simp only [PointedCone.hull, SetLike.mem_coe] at hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    rcases hx.1 j with h | h <;> simp [h]
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply]; linarith
  | smul c x _ hx =>
    simp only [Pi.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact mul_nonneg c.2 hx

theorem ls_Qd {ι : Type} [Fintype ι] [DecidableEq ι] (j : Option ι) :
    (Pi.single j (1:ℝ) : Option ι → ℝ) ∈ dualCone (Q : Set (Option ι → ℝ)) := by
  intro q hq
  simpa [single_dotProduct] using ls_Qnonneg q hq j

theorem ls_exp {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (a : ι → ℝ) :
    a ⬝ᵥ (Y *ᵥ a) = ∑ j, a j * (a ⬝ᵥ (Y *ᵥ Pi.single j 1)) := by
  simp only [mulVec_single_one]
  simp only [dotProduct, mulVec, Matrix.col, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  simp [transpose_apply]; ring

open Classical in
noncomputable def dS {ι : Type} (S : Set ι) : Option ι → ℝ :=
  fun o => Option.elim o 1 (fun i => if i ∈ S then 0 else 1)

noncomputable def Dop {ι : Type} (S : Set ι) (z : Option ι → ℝ) : Option ι → ℝ :=
  fun o => dS S o * z o

theorem dS_01 {ι : Type} (S : Set ι) (o : Option ι) : dS S o = 0 ∨ dS S o = 1 := by
  classical
  cases o with
  | none => right; rfl
  | some i => by_cases h : i ∈ S <;> simp [dS, h]

theorem dS_none {ι : Type} (S : Set ι) : dS S none = 1 := rfl

theorem Q_Dop {ι : Type} (S : Set ι) : ∀ q ∈ (Q : Set (Option ι → ℝ)), Dop S q ∈ Q := by
  intro q hq
  unfold Q cone at hq ⊢
  simp only [PointedCone.hull, SetLike.mem_coe] at hq ⊢
  induction hq using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · intro j
      rcases dS_01 S j with h | h <;> rcases hx.1 j with h' | h' <;> simp [Dop, h, h']
    · simp [Dop, dS_none, hx.2]
  | zero =>
    have : Dop S (0 : Option ι → ℝ) = 0 := by funext o; simp [Dop]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : Dop S (x + y) = Dop S x + Dop S y := by funext o; simp [Dop]; ring
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : Dop S (c • x) = c • Dop S x := by
      funext o; simp only [Dop, Pi.smul_apply]; exact mul_smul_comm _ _ _
    rw [this]; exact Submodule.smul_mem _ c hx

theorem Dop_dot {ι : Type} [Fintype ι] (S : Set ι) (u z : Option ι → ℝ) :
    Dop S u ⬝ᵥ z = u ⬝ᵥ Dop S z := by
  simp only [dotProduct, Dop]; apply Finset.sum_congr rfl; intro j _; ring

theorem N1plus_Dop {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set ι)
    (K : Set (Option ι → ℝ)) (hK : ∀ z ∈ K, Dop S z ∈ K) :
    ∀ z ∈ N1plus K, Dop S z ∈ N1plus K := by
  intro z hz
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hz
  let d := dS S
  let Y' : Matrix (Option ι) (Option ι) ℝ := diagonal d * Y * diagonal d
  have hY' : ∀ p q, Y' p q = d p * Y p q * d q := by
    intro p q; simp [Y', mul_apply, diagonal]
  have hdd : ∀ p, d p * d p = d p := by
    intro p; rcases dS_01 S p with h | h <;> simp [d, h]
  refine ⟨Y', ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · ext p q
    simp only [transpose_apply, hY']
    rw [hsym.apply]; ring
  · intro i
    rw [hY', hY', hdiag i]
    show d (some i) * Y none (some i) * d (some i) = d none * Y none (some i) * d (some i)
    rw [show d none = 1 from rfl]
    rcases dS_01 S (some i) with h | h <;> simp [d, h]
  · intro u hu v hv
    have : u ⬝ᵥ (Y' *ᵥ v) = Dop S u ⬝ᵥ (Y *ᵥ Dop S v) := by
      simp only [dotProduct, mulVec, hY', Dop, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      simp only [d]; ring
    rw [this]
    apply hMc
    · intro x hx; rw [Dop_dot]; exact hu _ (hK x hx)
    · intro x hx; rw [Dop_dot]; exact hv _ (Q_Dop S x hx)
  · have := hpsd.mul_mul_conjTranspose_same (diagonal d)
    simpa [diagonal_conjTranspose, Y'] using this
  · ext p
    simp only [mulVec, dotProduct, hY', Dop, Pi.single_apply]
    simp [d, dS_none]

theorem N1plus_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (c : ℝ) (hc : 0 ≤ c) :
    ∀ z ∈ N1plus K, c • z ∈ N1plus K := by
  intro z hz
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hz
  refine ⟨c • Y, ⟨⟨hsym.smul c, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; simp [hdiag i]
  · intro u hu v hv
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hc (hMc u hu v hv)
  · exact hpsd.smul hc
  · rw [smul_mulVec]

theorem N1plus_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (K : Set (Option V → ℝ)) (hK : K ⊆ FR G) : N1plus K ⊆ FR G := by
  intro z hz
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hz
  refine ⟨?_, ?_⟩
  · intro i
    have := hMc (Pi.single (some i) 1) (by
      intro x hx; simpa [single_dotProduct] using (hK hx).1 i) _ (ls_Qd none)
    simpa [single_dotProduct] using this
  · intro i j hij
    have := hMc (Pi.single none 1 - Pi.single (some i) 1 - Pi.single (some j) 1) (by
      intro x hx
      simp only [sub_dotProduct, single_dotProduct, one_mul]
      linarith [(hK hx).2 i j hij]) _ (ls_Qd none)
    simp only [sub_dotProduct, single_dotProduct, one_mul] at this
    linarith

theorem iter_props {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ) :
    NplusIter r (FR G) ⊆ FR G ∧
    (∀ c : ℝ, 0 ≤ c → ∀ z ∈ NplusIter r (FR G), c • z ∈ NplusIter r (FR G)) ∧
    (∀ S : Set V, ∀ z ∈ NplusIter r (FR G), Dop S z ∈ NplusIter r (FR G)) := by
  induction r with
  | zero =>
    refine ⟨le_rfl, ?_, ?_⟩
    · intro c hc z hz
      refine ⟨fun i => ?_, fun i j h => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hz.1 i)
      · simp only [Pi.smul_apply, smul_eq_mul]
        have := hz.2 i j h
        nlinarith
    · intro S z hz
      have hle : ∀ i, Dop S z (some i) ≤ z (some i) := by
        intro i; simp only [Dop]
        rcases dS_01 S (some i) with h | h <;> rw [h] <;> linarith [hz.1 i]
      refine ⟨fun i => ?_, fun i j h => ?_⟩
      · simp only [Dop]
        rcases dS_01 S (some i) with h | h <;> rw [h] <;> linarith [hz.1 i]
      · have := hz.2 i j h
        have h0 : Dop S z none = z none := by simp [Dop, dS_none]
        linarith [hle i, hle j]
  | succ r ih =>
    refine ⟨N1plus_FR G _ ih.1, fun c hc => N1plus_smul _ c hc, fun S => N1plus_Dop S _ (ih.2.2 S)⟩

theorem ls_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (r : ℕ)
    (hcontract : ∀ v, 0 < a v → Valid (NplusG r G) (contractCoeff G a v) (b - a v)) :
    Valid (NplusG (r + 1) G) a b := by
  classical
  obtain ⟨hKFR, hKsmul, hKD⟩ := iter_props G r
  set K := NplusIter r (FR G) with hKdef
  intro x hx
  have hxFR : hom x ∈ FR G := (iter_props G (r + 1)).1 hx
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, hYx⟩ := hx
  let ap : V → ℝ := fun w => max (a w) 0
  let c : Option V → ℝ := fun o => Option.elim o b (fun w => -ap w)
  have hb : 0 ≤ b := by
    have := hvalid (chi ∅) (subset_convexHull ℝ _ ⟨∅, by simp, rfl⟩)
    simpa [chi] using this
  -- validity of the contracted positive part on K
  have hwf : ∀ v, 0 < a v → ∀ z ∈ K,
      ∑ w, contractCoeff G ap v w * z (some w) ≤ (b - a v) * z none := by
    intro v hv z hz
    let S : Set V := {w | a w < 0}
    have hz' : Dop S z ∈ K := hKD S z hz
    have hzFR := hKFR hz'
    have hD0 : Dop S z none = z none := by simp [Dop, dS_none]
    have hsum : ∑ w, contractCoeff G ap v w * z (some w) =
        ∑ w, contractCoeff G a v w * Dop S z (some w) := by
      apply Finset.sum_congr rfl; intro w _
      simp only [contractCoeff, Dop, dS, Option.elim, ap, S, Set.mem_setOf_eq]
      by_cases hw : a w < 0
      · simp [hw, max_eq_right hw.le]
      · push_neg at hw
        simp [not_lt.mpr hw, max_eq_left hw]
    rw [hsum]
    obtain ⟨w0, hw0⟩ := hG v
    have hz0 : 0 ≤ z none := by
      have := hzFR.2 v w0 hw0; rw [hD0] at this; linarith [hzFR.1 v, hzFR.1 w0]
    rcases lt_or_eq_of_le hz0 with hpos | hzero
    · let x' : V → ℝ := fun w => Dop S z (some w) / z none
      have hx' : x' ∈ NplusG r G := by
        show hom x' ∈ K
        have : hom x' = (z none)⁻¹ • Dop S z := by
          funext o
          cases o with
          | none => simp [hom, hD0, hpos.ne']
          | some w => simp [hom, x', div_eq_inv_mul]
        rw [this]; exact hKsmul _ (inv_nonneg.mpr hz0) _ hz'
      have := hcontract v hv x' hx'
      simp only [x'] at this
      have heq : ∑ w, contractCoeff G a v w * Dop S z (some w) =
          z none * ∑ w, contractCoeff G a v w * (Dop S z (some w) / z none) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _
        field_simp
      rw [heq]
      nlinarith
    · have hall : ∀ w, Dop S z (some w) = 0 := by
        intro w
        obtain ⟨w1, hw1⟩ := hG w
        have := hzFR.2 w w1 hw1
        rw [hD0, ← hzero] at this
        linarith [hzFR.1 w, hzFR.1 w1]
      simp [hall, ← hzero]
  -- columns
  have hcol : ∀ v, 0 < a v → 0 ≤ c ⬝ᵥ (Y *ᵥ Pi.single (some v) 1) := by
    intro v hv
    set y := Y *ᵥ Pi.single (some v) 1 with hydef
    have hy : ∀ u ∈ dualCone K, 0 ≤ u ⬝ᵥ y := fun u hu => hMc u hu _ (ls_Qd _)
    have hyv : y (some v) = y none := by
      simp [hydef, mulVec_single_one, hdiag v]
    have hyw : ∀ w, 0 ≤ y (some w) := by
      intro w
      have := hy (Pi.single (some w) 1) (by
        intro z hz; simpa [single_dotProduct] using (hKFR hz).1 w)
      simpa [single_dotProduct] using this
    have hyadj : ∀ w, G.Adj v w → y (some w) = 0 := by
      intro w hvw
      have := hy (Pi.single none 1 - Pi.single (some v) 1 - Pi.single (some w) 1) (by
        intro z hz
        simp only [sub_dotProduct, single_dotProduct, one_mul]
        linarith [(hKFR hz).2 v w hvw])
      simp only [sub_dotProduct, single_dotProduct, one_mul] at this
      linarith [hyw w]
    let wf : Option V → ℝ := fun o => Option.elim o (b - a v) (fun w => -contractCoeff G ap v w)
    have hwfK : wf ∈ dualCone K := by
      intro z hz
      have := hwf v hv z hz
      simp only [dotProduct, Fintype.sum_option, wf, Option.elim]
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    have h1 := hy wf hwfK
    have hkey : ∑ w, (ap w - contractCoeff G ap v w) * y (some w) = a v * y (some v) := by
      rw [Finset.sum_eq_single v]
      · simp [contractCoeff, ap, max_eq_left hv.le]
      · intro w _ hwv
        by_cases hadj : G.Adj v w
        · simp [hyadj w hadj]
        · simp [contractCoeff, hwv, hadj]
      · simp
    have e1 : c ⬝ᵥ y = b * y none + ∑ w, -ap w * y (some w) := by
      simp [dotProduct, Fintype.sum_option, c]
    have e2 : wf ⬝ᵥ y = (b - a v) * y none + ∑ w, -contractCoeff G ap v w * y (some w) := by
      simp [dotProduct, Fintype.sum_option, wf]
    have e3 : ∑ w, -ap w * y (some w) = ∑ w, -contractCoeff G ap v w * y (some w)
        - ∑ w, (ap w - contractCoeff G ap v w) * y (some w) := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro w _; ring
    rw [e1, e3, hkey]
    rw [e2] at h1
    rw [hyv]; linarith
  -- PSD argument
  have hnn : 0 ≤ c ⬝ᵥ (Y *ᵥ c) := by simpa using hpsd.dotProduct_mulVec_nonneg c
  have hterm : ∀ v : V, c (some v) * (c ⬝ᵥ (Y *ᵥ Pi.single (some v) 1)) ≤ 0 := by
    intro v
    by_cases hv : 0 < a v
    · have : c (some v) = -a v := by simp [c, ap, max_eq_left hv.le]
      rw [this]; nlinarith [hcol v hv]
    · push_neg at hv
      have : c (some v) = 0 := by simp [c, ap, max_eq_right hv]
      rw [this, zero_mul]
  have hsumt : ∑ v : V, c (some v) * (c ⬝ᵥ (Y *ᵥ Pi.single (some v) 1)) ≤ 0 :=
    Finset.sum_nonpos (fun v _ => hterm v)
  have hc0 : c none = b := rfl
  rw [ls_exp, Fintype.sum_option, hc0] at hnn
  have hmain : 0 ≤ c ⬝ᵥ (Y *ᵥ Pi.single none 1) := by
    rcases lt_or_eq_of_le hb with hbpos | hbzero
    · by_contra hneg; push_neg at hneg
      have : b * (c ⬝ᵥ (Y *ᵥ Pi.single none 1)) < 0 := mul_neg_of_pos_of_neg hbpos hneg
      linarith
    · have hz : c ⬝ᵥ (Y *ᵥ c) = 0 := by
        rw [ls_exp, Fintype.sum_option, hc0, ← hbzero, zero_mul, zero_add]
        rw [← hbzero, zero_mul, zero_add] at hnn
        linarith
      have hYc : Y *ᵥ c = 0 := (hpsd.dotProduct_mulVec_zero_iff c).mp (by simpa using hz)
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym.eq, hYc, zero_dotProduct]
  rw [hYx] at hmain
  have e : c ⬝ᵥ hom x = b - ∑ w, ap w * x w := by
    simp [dotProduct, Fintype.sum_option, c, hom]; ring
  rw [e] at hmain
  have : ∑ i, a i * x i ≤ ∑ w, ap w * x w := by
    apply Finset.sum_le_sum; intro i _
    have hxi : 0 ≤ x i := hxFR.1 i
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxi
  linarith


end lssec

section gsec


theorem g_modsucc (m x : ℕ) (hx : x < m) : (x + 1) % m = if x + 1 = m then 0 else x + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem g_cyc3 (m s t u : ℕ) (hm : 5 ≤ m) (hs : s < m) (ht : t < m) (hu : u < m)
    (h1 : t = (s + 1) % m ∨ s = (t + 1) % m) (h2 : u = (s + 1) % m ∨ s = (u + 1) % m)
    (h3 : u = (t + 1) % m ∨ t = (u + 1) % m) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    False := by
  rw [g_modsucc m s hs, g_modsucc m t ht, g_modsucc m u hu] at *
  split_ifs at h1 h2 h3 <;> omega

theorem g_sum_chi {V : Type} [Fintype V] [DecidableEq V] (f : V → ℝ) (A : Finset V) :
    ∑ i, f i * chi A i = ∑ i ∈ A, f i := by
  simp [chi, mul_ite, Finset.sum_ite_mem]

theorem g_valid_hull {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (a : V → ℝ)
    (b : ℝ) (h : ∀ A : Finset V, G.IsIndepSet (A : Set V) → ∑ i ∈ A, a i ≤ b) :
    Valid (STAB G) a b := by
  have hlin : IsLinearMap ℝ (fun x : V → ℝ => ∑ i, a i * x i) :=
    ⟨fun x y => by simp [mul_add, Finset.sum_add_distrib],
     fun c x => by simp [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring⟩
  have hsub : STAB G ⊆ {x | ∑ i, a i * x i ≤ b} := by
    apply convexHull_min _ (convex_halfSpace_le hlin b)
    rintro x ⟨A, hA, rfl⟩
    show ∑ i, a i * chi A i ≤ b
    rw [g_sum_chi]; exact h A hA
  intro x hx; exact hsub hx

theorem g_contract_STAB {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (v : V) :
    Valid (STAB G) (contractCoeff G a v) (b - a v) := by
  apply g_valid_hull
  intro A hA
  let F := A.filter (fun w => ¬ (w = v ∨ G.Adj v w))
  have hvF : v ∉ F := by simp [F]
  have hind : G.IsIndepSet ((insert v F : Finset V) : Set V) := by
    intro x hx y hy hxy hadj
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, F, Finset.mem_filter] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact hxy rfl
    · exact hy.2 (Or.inr hadj)
    · exact hx.2 (Or.inr hadj.symm)
    · exact hA hx.1 hy.1 hxy hadj
  have h1 := hvalid _ (subset_convexHull ℝ _ ⟨_, hind, rfl⟩)
  rw [g_sum_chi, Finset.sum_insert hvF] at h1
  have h2 : ∑ i ∈ A, contractCoeff G a v i = ∑ i ∈ F, a i := by
    simp only [contractCoeff, F, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _
    split_ifs <;> simp_all
  rw [h2]; linarith

theorem g_hole_card {V : Type} [DecidableEq V] (G : SimpleGraph V) (C : Finset V)
    (hC : IsOddHole G C) (A : Finset V) (hA : G.IsIndepSet (A : Set V)) :
    2 * (A.filter (· ∈ C)).card + 1 ≤ C.card := by
  classical
  obtain ⟨m, hodd, hm3, f, hf⟩ := hC
  have hm : m % 2 = 1 := Nat.odd_iff.mp hodd
  have hmC : C.card = m := by
    have := Fintype.card_congr f; simp at this; omega
  let T : Finset (Fin m) := Finset.univ.filter (fun s => ((f s : C) : V) ∈ A)
  have hTA : A.filter (· ∈ C) = T.image (fun s => ((f s : C) : V)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, T]
    constructor
    · rintro ⟨hwA, hwC⟩
      exact ⟨f.symm ⟨w, hwC⟩, by simpa using hwA, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, (f s).2⟩
  have hcard : (A.filter (· ∈ C)).card = T.card := by
    rw [hTA]; apply Finset.card_image_of_injective
    intro s t h; exact f.injective (Subtype.ext h)
  let σ : Fin m → Fin m := fun s => ⟨(s.val + 1) % m, Nat.mod_lt _ (by omega)⟩
  have hσ : Function.Injective σ := by
    intro s t h
    have h' : (s.val + 1) % m = (t.val + 1) % m := congrArg Fin.val h
    rw [g_modsucc m _ s.2, g_modsucc m _ t.2] at h'
    apply Fin.ext
    split_ifs at h' <;> omega
  have hdisj : Disjoint T (T.image σ) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T] at hs ht
    have hadj : G.Adj ((f t : C) : V) ((f (σ t) : C) : V) := (hf _ _).mpr (Or.inl rfl)
    rw [hts] at hadj
    exact hA ht hs (G.ne_of_adj hadj) hadj
  have hle : (T ∪ T.image σ).card ≤ m := by
    have := Finset.card_le_univ (T ∪ T.image σ); simpa using this
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hσ] at hle
  omega

theorem g_antihole_card {V : Type} [DecidableEq V] (G : SimpleGraph V) (D : Finset V)
    (hD : IsOddAntihole G D) (A : Finset V) (hA : G.IsIndepSet (A : Set V)) :
    (A.filter (· ∈ D)).card ≤ 2 := by
  classical
  obtain ⟨hD5, m, hodd, hm3, f, hf⟩ := hD
  have hmC : D.card = m := by
    have := Fintype.card_congr f; simp at this; omega
  let T : Finset (Fin m) := Finset.univ.filter (fun s => ((f s : D) : V) ∈ A)
  have hTA : A.filter (· ∈ D) = T.image (fun s => ((f s : D) : V)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, T]
    constructor
    · rintro ⟨hwA, hwC⟩
      exact ⟨f.symm ⟨w, hwC⟩, by simpa using hwA, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs, (f s).2⟩
  have hcard : (A.filter (· ∈ D)).card = T.card := by
    rw [hTA]; apply Finset.card_image_of_injective
    intro s t h; exact f.injective (Subtype.ext h)
  rw [hcard]
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := Finset.two_lt_card.mp hlt
  have cyc : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → (y.val = (x.val + 1) % m ∨ x.val = (y.val + 1) % m) := by
    intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T] at hx hy
    have hne : ((f x : D) : V) ≠ ((f y : D) : V) := by
      intro h; exact hxy (f.injective (Subtype.ext h))
    apply (hf x y).mp
    rw [SimpleGraph.compl_adj]
    exact ⟨hne, fun h => hA hx hy hne h⟩
  exact g_cyc3 m s t u (by omega) s.2 t.2 u.2 (cyc s hs t ht hst) (cyc s hs u hu hsu)
    (cyc t ht u hu htu) (fun h => hst (Fin.ext h)) (fun h => hsu (Fin.ext h))
    (fun h => htu (Fin.ext h))


end gsec

theorem goal_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi B) 1} 1) ∧
    (∀ C : Finset V, IsOddHole G C →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi C) (((C.card : ℝ) - 1) / 2)} 1) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ →
        IsLeast {t : ℕ | Valid (NplusG t G) (wheelCoeff U u₀) (((U.card : ℝ) - 2) / 2)} 1) ∧
    (∀ D : Finset V, IsOddAntihole G D →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi D) 2} 1) := by
  classical
  have lvl1 : ∀ (a : V → ℝ) (b : ℝ), (∀ i, 0 ≤ a i) → Valid (STAB G) a b →
      (∀ v, 0 < a v → (G.induce {w | 0 < contractCoeff G a v w}).Colorable 2) →
      Valid (NplusG 1 G) a b := by
    intro a b hnn hv hbip
    apply ls_core G hG a b hv 0
    intro v hav x hx
    have hxF : x ∈ FRAC G := by
      obtain ⟨h1, h2⟩ := hx
      exact ⟨fun i => h1 i, fun i j h => by simpa [hom] using h2 i j h⟩
    have hset : {i | contractCoeff G a v i ≠ 0} = {w | 0 < contractCoeff G a v w} := by
      ext w
      simp only [Set.mem_setOf_eq]
      have h0 : 0 ≤ contractCoeff G a v w := by
        unfold contractCoeff; split_ifs
        · exact le_rfl
        · exact hnn w
      constructor
      · intro h; exact lt_of_le_of_ne h0 (Ne.symm h)
      · intro h; exact ne_of_gt h
    have hb2 := hbip v hav
    rw [← hset] at hb2
    exact vfb_core G hG _ _ (g_contract_STAB G a b hv v) hb2 x hxF
  have half : (fun _ => (1/2 : ℝ)) ∈ NplusG 0 G := by
    show hom _ ∈ FR G
    refine ⟨fun i => ?_, fun i j _ => ?_⟩ <;> norm_num [hom]
  have least : ∀ (a : V → ℝ) (b : ℝ), Valid (NplusG 1 G) a b →
      b < ∑ i, a i * (1/2 : ℝ) → IsLeast {t : ℕ | Valid (NplusG t G) a b} 1 := by
    intro a b h1 hlt
    refine ⟨h1, fun t ht => ?_⟩
    by_contra h0
    have : t = 0 := by omega
    subst this
    have := ht _ half
    linarith
  have sumhalf : ∀ (A : Finset V), ∑ i, chi A i * (1/2 : ℝ) = (A.card : ℝ) / 2 := by
    intro A
    have : ∀ i, chi A i * (1/2 : ℝ) = (fun _ => (1/2 : ℝ)) i * chi A i := fun i => mul_comm _ _
    simp only [this, g_sum_chi]
    simp; ring
  have chinn : ∀ (A : Finset V) i, 0 ≤ chi A i := by
    intro A i; unfold chi; split_ifs <;> norm_num
  have sumchiA : ∀ (A X : Finset V), ∑ i ∈ A, chi X i = ((A.filter (· ∈ X)).card : ℝ) := by
    intro A X; simp [chi]; rw [Finset.filter_mem_eq_inter]
  have holecard : ∀ C : Finset V, IsOddHole G C → 3 ≤ C.card := by
    intro C hC
    obtain ⟨m, _, hm3, f, _⟩ := hC
    have := Fintype.card_congr f; simp at this; omega
  have hcsb := csb_core G hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B hB h3
    apply least
    · apply lvl1 _ _ (chinn B) _ (hcsb.1 B hB h3)
      apply g_valid_hull
      intro A hA
      rw [sumchiA]
      have : (A.filter (· ∈ B)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro x hx y hy
        simp only [Finset.mem_filter] at hx hy
        by_contra hne
        exact hA hx.1 hy.1 hne (hB hx.2 hy.2 hne)
      exact_mod_cast this
    · rw [sumhalf]
      have : (3 : ℝ) ≤ B.card := by exact_mod_cast h3
      linarith
  · intro C hC
    apply least
    · apply lvl1 _ _ (chinn C) _ (hcsb.2.1 C hC)
      apply g_valid_hull
      intro A hA
      rw [sumchiA]
      have := g_hole_card G C hC A hA
      have : (2 * (A.filter (· ∈ C)).card + 1 : ℝ) ≤ C.card := by exact_mod_cast this
      linarith
    · rw [sumhalf]; linarith
  · intro U u₀ hW
    obtain ⟨hu₀, hC, hadj⟩ := hW
    set C := U.erase u₀ with hCdef
    have hC3 := holecard C hC
    have hUC : (C.card : ℝ) + 1 = U.card := by
      have := Finset.card_erase_add_one hu₀
      rw [← hCdef] at this
      exact_mod_cast this
    have hC3r : (3 : ℝ) ≤ C.card := by exact_mod_cast hC3
    have hnn : ∀ i, 0 ≤ wheelCoeff U u₀ i := by
      intro i; unfold wheelCoeff; split_ifs
      · linarith
      · norm_num
      · norm_num
    apply least
    · apply lvl1 _ _ hnn _ (hcsb.2.2.1 U u₀ ⟨hu₀, hC, hadj⟩)
      apply g_valid_hull
      intro A hA
      by_cases hA0 : u₀ ∈ A
      · rw [← Finset.add_sum_erase _ _ hA0]
        have : ∑ x ∈ A.erase u₀, wheelCoeff U u₀ x = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          obtain ⟨hiu, hiA⟩ := Finset.mem_erase.mp hi
          have hiU : i ∉ U := by
            intro hiU
            have := hadj i (Finset.mem_erase.mpr ⟨hiu, hiU⟩)
            exact hA hA0 hiA (Ne.symm hiu) this
          simp [wheelCoeff, hiu, hiU]
        rw [this]; simp [wheelCoeff]
      · have : ∑ i ∈ A, wheelCoeff U u₀ i = ∑ i ∈ A, chi C i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiu : i ≠ u₀ := fun h => hA0 (h ▸ hi)
          simp [wheelCoeff, chi, hiu, hCdef, Finset.mem_erase]
        rw [this, sumchiA]
        have := g_hole_card G C hC A hA
        have : (2 * (A.filter (· ∈ C)).card + 1 : ℝ) ≤ C.card := by exact_mod_cast this
        linarith
    · have hw : ∀ i, wheelCoeff U u₀ i =
          (if i = u₀ then ((U.card : ℝ) - 2) / 2 else 0) + chi C i := by
        intro i
        by_cases hiu : i = u₀
        · subst hiu; simp [wheelCoeff, chi, hCdef]
        · simp [wheelCoeff, chi, hiu, hCdef, Finset.mem_erase]
      have hs : ∑ i, wheelCoeff U u₀ i * (1/2 : ℝ) =
          (((U.card : ℝ) - 2) / 2) * (1/2) + (C.card : ℝ) / 2 := by
        simp only [hw, add_mul, Finset.sum_add_distrib, sumhalf]
        simp
      rw [hs]
      linarith
  · intro D hD
    apply least
    · apply lvl1 _ _ (chinn D) _ (hcsb.2.2.2 D hD)
      apply g_valid_hull
      intro A hA
      rw [sumchiA]
      have := g_antihole_card G D hD A hA
      exact_mod_cast this
    · rw [sumhalf]
      have : (5 : ℝ) ≤ D.card := by exact_mod_cast hD.1
      linarith

end LovaszSchrijver.NPlus

open LovaszSchrijver.NPlus


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi B) 1} 1) ∧
    (∀ C : Finset V, IsOddHole G C →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi C) (((C.card : ℝ) - 1) / 2)} 1) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ →
        IsLeast {t : ℕ | Valid (NplusG t G) (wheelCoeff U u₀) (((U.card : ℝ) - 2) / 2)} 1) ∧
    (∀ D : Finset V, IsOddAntihole G D →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi D) 2} 1) := by
  exact goal_core G hG
