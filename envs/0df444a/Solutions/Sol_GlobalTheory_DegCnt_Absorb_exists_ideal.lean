-- Prove2me | solution 1 for GlobalTheory.DegCnt.Absorb.exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:19.554732+00:00
-- url     : https://prove2.me/submissions/fb877f02-7e84-4069-8707-3fd51b39fe3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_nat
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_mem_ipow_iff
import Theorems.Thm_GlobalTheory_DegCnt_Absorb_exists_coord
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_dual_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
namespace GlobalTheory.DegCnt.Absorb
section Ideals
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K]
end Ideals
section Flags
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private theorem fractionalIdeal_zpow_sum_eq_prod (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) (s : Finset ℕ)
    (f : ℕ → ℤ) : J ^ (∑ a ∈ s, f a) = ∏ a ∈ s, J ^ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hJ, ih]
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem lead_eq_ipow_of_isFrame (N : _root_.GlobalTheory.DegCnt.NF H r) {F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r}
    {Λ : Submodule (𝓞 K) V} (hF : _root_.GlobalTheory.HermLat.IsFrame F Λ N.aa) (a : Fin (r + 1)) :
    _root_.GlobalTheory.HermLat.lead F Λ a = _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-((r : ℤ) - a)) := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
  · rw [hF.1 b]; rfl
  · rw [hF.2]; simp [_root_.GlobalTheory.DegCnt.ipow]
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem exists_mem_pow_eq_star (N : _root_.GlobalTheory.DegCnt.NF H r) (k : ℕ) {d : 𝓞 K}
    (hd : d ∈ N.𝔡 ^ k) : ∃ d' ∈ N.𝔡 ^ k, (d' : K) = star (d : K) := by
  have h1 : N.𝔡 ≤ N.𝔡.comap (_root_.GlobalTheory.DegCnt.Absorb.sig K : 𝓞 K →+* 𝓞 K) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := N.𝔡_star x hx
    have : (_root_.GlobalTheory.DegCnt.Absorb.sig K x : 𝓞 K) = y := by
      ext; exact hyx.symm
    rw [Ideal.mem_comap]
    simpa [this] using hy
  have h2 := (Ideal.pow_right_mono h1 k).trans (Ideal.le_comap_pow _ k) hd
  exact ⟨_, h2, rfl⟩
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem star_mem_ipow_neg_of_nonneg (N : _root_.GlobalTheory.DegCnt.NF H r) {n : ℤ}
    (hn : 0 ≤ n) {t : K} (ht : t ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-n)) :
    star t ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-n) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_iff N.𝔡_ne, neg_neg] at ht ⊢
  intro u hu
  obtain ⟨d, hd, rfl⟩ := (_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).1 hu
  obtain ⟨d', hd', hdd'⟩ := exists_mem_pow_eq_star N k hd
  have h3 := ht _ ((_root_.GlobalTheory.DegCnt.Absorb.mem_ipow_nat _ _ _).2 ⟨d', hd', rfl⟩)
  rw [hdd'] at h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 h3
  refine Submodule.mem_one.2 ⟨_root_.GlobalTheory.DegCnt.Absorb.sig K o, ?_⟩
  have e1 : algebraMap (𝓞 K) K (_root_.GlobalTheory.DegCnt.Absorb.sig K o) =
      star (algebraMap (𝓞 K) K o) := rfl
  rw [e1, ho, star_mul, star_star, mul_comm]
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private theorem mul_mem_of_forall_prod_mem {ι : Type} (s : Finset ι) (I : ι → FractionalIdeal (𝓞 K)⁰ K)
    (M : Submodule (𝓞 K) K) (x : K)
    (hx : ∀ g : ι → K, (∀ i ∈ s, g i ∈ I i) → x * ∏ i ∈ s, g i ∈ M) :
    ∀ u ∈ (∏ i ∈ s, I i), x * u ∈ M := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    intro u hu
    rw [Finset.prod_empty, FractionalIdeal.mem_one_iff] at hu
    obtain ⟨o, rfl⟩ := hu
    have h0 := hx (fun _ => 0) (by simp)
    rw [Finset.prod_empty, mul_one] at h0
    rw [mul_comm, ← Algebra.smul_def]
    exact M.smul_mem o h0
  | insert i s hi ih =>
    intro u hu
    rw [Finset.prod_insert hi] at hu
    refine FractionalIdeal.mul_induction_on hu ?_ ?_
    · intro p hp q hq
      rw [← mul_assoc]
      refine ih (x * p) (fun g hg => ?_) q hq
      have hne : ∀ j ∈ s, j ≠ i := fun j hj hji => hi (hji ▸ hj)
      have h1 := hx (Function.update g i p) (by
        intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simpa using hp
        · rw [Function.update_of_ne (hne j hj)]; exact hg j hj)
      rwa [Finset.prod_insert hi, Function.update_self,
        Finset.prod_congr rfl (fun j hj => Function.update_of_ne (hne j hj) _ _), ← mul_assoc] at h1
    · intro y z hy hz
      rw [mul_add]
      exact M.add_mem hy hz
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem exists_triangular_lattice_vectors (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r) (Λ : Submodule (𝓞 K) V)
    {l : ℕ} (hl : l ≤ r + 1) (u : Fin l → K)
    (hu : ∀ a, u a ∈ _root_.GlobalTheory.HermLat.lead F Λ (Fin.castLE hl a)) :
    ∃ P : Matrix (Fin l) (Fin l) K, P.det = ∏ a, u a ∧
      ∀ a, ∑ b, P a b • F.e (Fin.castLE hl b) ∈ Λ := by
  have hx : ∀ a : Fin l, ∃ m : Fin l → K, (∀ b, a ≤ b → m b = 0) ∧
      u a • F.e (Fin.castLE hl a) - ∑ b, m b • F.e (Fin.castLE hl b) ∈ Λ := by
    intro a
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hu a)
    obtain ⟨m, hm, rfl⟩ := _root_.GlobalTheory.DegCnt.Absorb.exists_coord F hl a (by simpa using hz)
    refine ⟨m, hm, ?_⟩
    have : u a • F.e (Fin.castLE hl a) = y + ∑ b, m b • F.e (Fin.castLE hl b) := hyz.symm
    rw [this, add_sub_cancel_right]
    exact hy
  choose m hm hmΛ using hx
  refine ⟨Matrix.of fun a b => (if a = b then u a else 0) - m a b, ?_, ?_⟩
  · have hP : (Matrix.of fun a b => (if a = b then u a else 0) - m a b).BlockTriangular
        OrderDual.toDual := by
      intro a b hab
      have hab' : a < b := hab
      simp [hab'.ne, hm a b hab'.le]
    rw [Matrix.det_of_lowerTriangular _ hP]
    exact Finset.prod_congr rfl fun a _ => by simp [hm a a le_rfl]
  · intro a
    convert hmΛ a using 1
    simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private theorem det_mem_one_of_entries_mem_one {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n K)
    (hX : ∀ i j, X i j ∈ (1 : Submodule (𝓞 K) K)) : X.det ∈ (1 : Submodule (𝓞 K) K) := by
  choose Y hY using fun i j => Submodule.mem_one.1 (hX i j)
  have hXY : X = (algebraMap (𝓞 K) K).mapMatrix (Matrix.of Y) := by
    ext i j; simp [hY]
  rw [hXY, ← RingHom.map_det]
  exact Submodule.mem_one.2 ⟨_, rfl⟩
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem hermForm_combinations_eq_gram_mul {l : ℕ} (P Q : Matrix (Fin l) (Fin l) K) (F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
    (hl : l ≤ r + 1) (a c : Fin l) :
    H.B (∑ b, P a b • F.e (Fin.castLE hl b)) (∑ d, Q c d • F'.e (Fin.castLE hl d)) =
      (P * (_root_.Formalism.HermitianLatticeCounting.S6.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl) * (Q.map star).transpose) a c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
    _root_.Formalism.HermitianLatticeCounting.S6.Zhat, Matrix.of_apply, map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
  simp [starRingEnd_apply]; ring
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem hermForm_mem_one_of_isFramed {F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} {Λ : Submodule (𝓞 K) V}
    {I : Fin r → Submodule (𝓞 K) K} (h : _root_.GlobalTheory.HermLat.IsFramed F F' Λ I) {x y : V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
  have hd := h.1.2
  rw [← hd] at hx
  exact ((_root_.GlobalTheory.HermLat.mem_dual_iff H Λ x).1 hx).2 y hy
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem prod_mul_Dl_mul_star_prod_mem_one {F F' : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r} {Λ : Submodule (𝓞 K) V}
    {I : Fin r → Submodule (𝓞 K) K} (h : _root_.GlobalTheory.HermLat.IsFramed F F' Λ I) {l : ℕ}
    (hl : l ≤ r + 1) (t s : Fin l → K)
    (ht : ∀ a, t a ∈ _root_.GlobalTheory.HermLat.lead F Λ (Fin.castLE hl a))
    (hs : ∀ a, s a ∈ _root_.GlobalTheory.HermLat.lead F' Λ (Fin.castLE hl a)) :
    (∏ a, t a) * _root_.Formalism.HermitianLatticeCounting.S6.Dl F F' l hl * star (∏ a, s a) ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨P, hP, hPΛ⟩ := exists_triangular_lattice_vectors F Λ hl t ht
  obtain ⟨Q, hQ, hQΛ⟩ := exists_triangular_lattice_vectors F' Λ hl s hs
  have hX := det_mem_one_of_entries_mem_one
    (P * (_root_.Formalism.HermitianLatticeCounting.S6.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl) * (Q.map star).transpose)
    fun a c => by
      rw [← hermForm_combinations_eq_gram_mul]
      exact hermForm_mem_one_of_isFramed h (hPΛ a) (hQΛ c)
  have hs' : (Q.map star).det = star Q.det := ((starRingEnd K).map_det Q).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs', hP, hQ] at hX
  exact hX
open NumberField in
open scoped Pointwise ENNReal Classical nonZeroDivisors in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} in
private theorem Dl_mul_mem_one_of_mem_ipow (N : _root_.GlobalTheory.DegCnt.NF H r) {Λ : Submodule (𝓞 K) V}
    (h : _root_.GlobalTheory.HermLat.IsFramed N.F N.F' Λ N.aa) {l : ℕ} (hl : l ≤ r + 1) {u : K}
    (hu : u ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)))) :
    _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl * u ∈ (1 : Submodule (𝓞 K) K) := by
  have hJ : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact N.𝔡_ne
  have heq : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a))) =
      (∏ a ∈ Finset.range l, (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a))) *
        ∏ a ∈ Finset.range l, (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a)) := by
    rw [← fractionalIdeal_zpow_sum_eq_prod _ hJ, ← zpow_add₀ hJ, Finset.sum_neg_distrib]
    congr 1
    ring
  rw [heq] at hu
  have hmem : ∀ (a : Fin l) {v : K}, v ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-((r : ℤ) - a)) →
      v ∈ _root_.GlobalTheory.HermLat.lead N.F Λ (Fin.castLE hl a) ∧
        star v ∈ _root_.GlobalTheory.HermLat.lead N.F' Λ (Fin.castLE hl a) := by
    intro a v hv
    have hv' : v ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (-((r : ℤ) - a)) := hv
    rw [lead_eq_ipow_of_isFrame N h.2.1, lead_eq_ipow_of_isFrame N h.2.2, Fin.coe_castLE]
    refine ⟨hv', star_mem_ipow_neg_of_nonneg N ?_ hv'⟩
    have := a.isLt
    omega
  refine FractionalIdeal.mul_induction_on hu ?_ ?_
  · intro p hp q hq
    rw [← mul_assoc]
    refine mul_mem_of_forall_prod_mem _ _ _ _ (fun g hg => ?_) q hq
    rw [mul_right_comm]
    refine mul_mem_of_forall_prod_mem _ _ _ _ (fun g' hg' => ?_) p hp
    have key := prod_mul_Dl_mul_star_prod_mem_one h hl (fun a => g' a) (fun a => star (g a))
      (fun a => (hmem a (hg' a (Finset.mem_range.2 a.isLt))).1)
      (fun a => (hmem a (hg a (Finset.mem_range.2 a.isLt))).2)
    have hst := map_prod (starRingEnd K) (fun a : Fin l => star (g a)) Finset.univ
    simp only [starRingEnd_apply, star_star] at hst
    rw [hst, Fin.prod_univ_eq_prod_range (fun a => g' a) l,
      Fin.prod_univ_eq_prod_range (fun a => g a) l] at key
    convert key using 1
    ring
  · intro y z hy hz
    rw [mul_add]
    exact add_mem hy hz
end Flags
end GlobalTheory.DegCnt.Absorb
end
end

set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.Absorb
namespace _root_.GlobalTheory.DegCnt.Absorb
theorem _root_.solution (N : _root_.GlobalTheory.DegCnt.NF H r) {Λ : Submodule (𝓞 K) V}
    (h : _root_.GlobalTheory.HermLat.IsFramed N.F N.F' Λ N.aa) (l : ℕ) :
    ∃ A : Ideal (𝓞 K), A ≠ ⊥ ∧ ∀ hl : l ≤ r + 1, l ≤ N.j → _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ≠ 0 →
      (Ideal.absNorm A : ℝ) = N.nD l ∧ ∀ x ∈ A, ∀ y ∈ _root_.GlobalTheory.DegCnt.ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)),
        (x : K) * y / _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) := by
  by_cases hl : l ≤ r + 1
  swap
  · exact ⟨⊤, top_ne_bot, fun hl' => absurd hl' hl⟩
  by_cases hD : _root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl = 0
  · exact ⟨⊤, top_ne_bot, fun _ _ hD' => absurd hD hD'⟩
  set e : ℤ := 2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a) with he
  have hJ : (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact N.𝔡_ne
  set I : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (_root_.Formalism.HermitianLatticeCounting.S6.Dl N.F N.F' l hl) * (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-e)
    with hI
  have hI1 : I ≤ 1 := by
    rw [hI, FractionalIdeal.mul_le]
    intro p hp q hq
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hp
    have := Dl_mul_mem_one_of_mem_ipow N h hl hq
    rw [smul_mul_assoc, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
    exact Submodule.smul_mem _ z this
  obtain ⟨A, hA⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hI1
  have hI0 : I ≠ 0 := by
    rw [hI]
    exact mul_ne_zero (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]) (zpow_ne_zero _ hJ)
  refine ⟨A, ?_, fun hl' _ hD' => ⟨?_, ?_⟩⟩
  · rintro rfl
    apply hI0
    rw [← hA, FractionalIdeal.coeIdeal_bot]
  · have hn := congrArg FractionalIdeal.absNorm hA
    rw [FractionalIdeal.coeIdeal_absNorm, hI, map_mul, map_zpow₀, FractionalIdeal.absNorm_span_singleton,
      FractionalIdeal.coeIdeal_absNorm] at hn
    unfold _root_.GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl']
    have hq := congrArg (fun q : ℚ => (q : ℝ)) hn
    push_cast at hq
    rw [hq]
  · intro x hx y hy
    have hx' : (x : K) ∈ I := by
      rw [← hA]; exact (FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩
    have hy' : y ∈ (N.𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ e := hy
    have hxy := FractionalIdeal.mul_mem_mul hx' hy'
    rw [hI, mul_assoc, ← zpow_add₀ hJ, neg_add_cancel, zpow_zero, mul_one] at hxy
    obtain ⟨z, hz⟩ := (FractionalIdeal.mem_spanSingleton _).1 hxy
    rw [← hz, Algebra.smul_def, mul_div_assoc, div_self hD', mul_one]
    exact Submodule.mem_one.2 ⟨z, rfl⟩
end _root_.GlobalTheory.DegCnt.Absorb
end GlobalTheory.DegCnt.Absorb
