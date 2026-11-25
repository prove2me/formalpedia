-- Prove2me | solution 1 for GlobalTheory.CharGerm.exists_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:33:39.703807+00:00
-- url     : https://prove2.me/submissions/ea54ea2c-0572-46f0-9206-ae2738df2559

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_GlobalTheory_CharGerm_coeff_mem_of_mem_truncI
import Theorems.Thm_GlobalTheory_CharGerm_truncI_X
import Theorems.Thm_GlobalTheory_CharGerm_truncI_p
import Theorems.Thm_GlobalTheory_CharGerm_aeval_eq_sum
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
variable {R₀ κ : Type} [CommRing R₀]
namespace GlobalTheory.CharGerm
theorem _root_.solution [Fintype κ] [DecidableEq κ] (p : ℕ)
    [IsPrecomplete (Ideal.span {(p : R₀)}) R₀]
    (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S)
    (hc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
      (φ : S →ₐ[R₀] S') (a : κ → S), IsNilpotent (p : S) →
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) :
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S) (N : ℕ),
      (p : S) ^ N = 0 → (∀ i, a i ^ N = 0) → c S a = tEval N f a := by
  choose P hP using fun N : ℕ => Ideal.Quotient.mk_surjective (I := truncI R₀ κ p N)
    (c (MvPolynomial κ R₀ ⧸ truncI R₀ κ p N)
      (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (p : S) ^ N = 0 →
      (∀ i, a i ^ N = 0) → c S a = MvPolynomial.aeval a (P N) := by
    intro N S _ _ a hp ha
    let φ : (MvPolynomial κ R₀ ⧸ truncI R₀ κ p N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (truncI R₀ κ p N) (MvPolynomial.aeval a) (by
        intro x hx
        have : truncI R₀ κ p N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ (rfl | ⟨j, rfl⟩)
          · simp [RingHom.mem_ker, hp]
          · simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (truncI R₀ κ p N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j))
      ⟨N, truncI_p p N⟩ (fun j => ⟨N, truncI_X p N j⟩)
    rw [← hP N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      MvPolynomial.coeff m (P N) - MvPolynomial.coeff m (P M) ∈ Ideal.span {(p : R₀) ^ N} := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j))
      (pow_eq_zero_of_le h (truncI_p p N))
      (fun j => pow_eq_zero_of_le h (truncI_X p N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (truncI R₀ κ p N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (truncI R₀ κ p N) := by
      ext j; simp
    rw [← hP N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := coeff_mem_of_mem_truncI h1 m hm
    rwa [MvPolynomial.coeff_sub] at h3
  have hI : ∀ n : ℕ, (Ideal.span {(p : R₀)} ^ n • ⊤ : Submodule R₀ R₀) =
      Ideal.span {(p : R₀) ^ n} := fun n => by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have hle : ∀ {n n' : ℕ}, n ≤ n' → Ideal.span {(p : R₀) ^ n'} ≤ Ideal.span {(p : R₀) ^ n} :=
    fun h => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have lim : ∀ m : κ →₀ ℕ, ∃ L : R₀, ∀ n,
      MvPolynomial.coeff m (P (n + (Finset.univ.sup m + 1))) - L ∈ Ideal.span {(p : R₀) ^ n} := by
    intro m
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R₀)}) (M := R₀) inferInstance
      (f := fun n => MvPolynomial.coeff m (P (n + (Finset.univ.sup m + 1)))) (by
        intro n n' h
        rw [hI, SModEq.sub_mem]
        refine hle (Nat.le_add_right _ _) (compat _ _ (by omega) m fun j => ?_)
        have := Finset.le_sup (f := m) (Finset.mem_univ j)
        omega)
    refine ⟨L, fun n => ?_⟩
    have := hL n
    rwa [hI, SModEq.sub_mem] at this
  choose L hL using lim
  refine ⟨L, ?_⟩
  intro S _ _ a N hp hN
  rw [key N S a hp hN, aeval_eq_sum hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = algebraMap R₀ S (L m)
  have h1 := add_mem (compat N _ (Nat.le_add_right N (Finset.univ.sup m + 1)) m
    (fun j => by simp [hm])) (hL m N)
  rw [sub_add_sub_cancel] at h1
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
  rw [← sub_eq_zero, ← map_sub, ← hr, map_mul, map_pow, map_natCast, hp, mul_zero]
end GlobalTheory.CharGerm
