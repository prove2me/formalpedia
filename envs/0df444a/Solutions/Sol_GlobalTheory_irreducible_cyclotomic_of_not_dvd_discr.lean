-- Prove2me | solution 1 for GlobalTheory.irreducible_cyclotomic_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:01:26.895711+00:00
-- url     : https://prove2.me/submissions/286fff4e-0c22-4d74-8708-4f115c1c6fcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Polynomial
namespace GlobalTheory
private lemma natAbs_eq_one_of_dvd_prime_pow_not_dvd {d : ℤ} {m k : ℕ} (hm : m.Prime) (h1 : d ∣ (m : ℤ) ^ k)
    (h2 : ¬ (m : ℤ) ∣ d) : d.natAbs = 1 := by
  have h1' : d.natAbs ∣ m ^ k := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa [Int.natAbs_pow] using this
  have hc : Nat.Coprime m d.natAbs := by
    rw [hm.coprime_iff_not_dvd]
    intro h
    exact h2 (Int.natCast_dvd.mpr h)
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hc).symm h1'
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [NumberField K] (m : ℕ)
    (hm : m.Prime) (hd : ¬ (m : ℤ) ∣ discr K) : Irreducible (cyclotomic m K) := by
  have : NeZero m := ⟨hm.ne_zero⟩
  have : Fact m.Prime := ⟨hm⟩
  let E := CyclotomicField m K
  have : FiniteDimensional ℚ E := Module.Finite.trans K E
  have hζ := IsCyclotomicExtension.zeta_spec m K E
  set ζ := IsCyclotomicExtension.zeta m K E
  let A : IntermediateField ℚ E := IntermediateField.adjoin ℚ {ζ}
  let B : IntermediateField ℚ E := (IsScalarTower.toAlgHom ℚ K E).fieldRange
  have hAc : IsCyclotomicExtension {m} ℚ A := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hGal : IsGalois ℚ A := IsCyclotomicExtension.isGalois {m} ℚ A
  have hinf : A ⊓ B = ⊥ := by
    let F : IntermediateField ℚ E := A ⊓ B
    let _ : Algebra F A := (IntermediateField.inclusion (inf_le_left : F ≤ A)).toRingHom.toAlgebra
    let _ : Algebra F K := (((IsScalarTower.toAlgHom ℚ K E).equivFieldRange.symm.toAlgHom).comp
      (IntermediateField.inclusion (inf_le_right : F ≤ B))).toRingHom.toAlgebra
    have hFA : NumberField.discr F ∣ NumberField.discr A := NumberField.discr_dvd_discr F A
    have hFK : NumberField.discr F ∣ NumberField.discr K := NumberField.discr_dvd_discr F K
    have hA : NumberField.discr A = (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2) :=
      IsCyclotomicExtension.Rat.discr_prime m A
    have hpow : NumberField.discr F ∣ (m : ℤ) ^ (m - 2) := by
      have : NumberField.discr F ∣ (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2) := hA ▸ hFA
      exact (IsUnit.dvd_mul_left ((isUnit_neg_one).pow _)).mp this
    have hnd : ¬ (m : ℤ) ∣ NumberField.discr F := fun h => hd (h.trans hFK)
    have h1 : (NumberField.discr F).natAbs = 1 := natAbs_eq_one_of_dvd_prime_pow_not_dvd hm hpow hnd
    have hrank : Module.finrank ℚ F = 1 := by
      by_contra hne
      have hgt : 1 < Module.finrank ℚ F := lt_of_le_of_ne Module.finrank_pos (Ne.symm hne)
      have h2 := NumberField.abs_discr_gt_two hgt
      rw [Int.abs_eq_natAbs, h1] at h2
      norm_num at h2
    exact IntermediateField.finrank_eq_one_iff.mp hrank
  have hdis : A.LinearDisjoint B :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot _ _ _ _ _ A B (by exact hGal) _ _ hinf
  have e1 : (IsScalarTower.toAlgHom ℚ K E).range = B.toSubalgebra :=
    (AlgHom.fieldRange_toSubalgebra _).symm
  have hdisK : A.LinearDisjoint K := by
    rw [IntermediateField.linearDisjoint_iff, e1]
    exact IntermediateField.linearDisjoint_iff'.mp hdis
  have hrk : Module.rank K (IntermediateField.adjoin K (A : Set E)) = Module.rank ℚ A :=
    hdisK.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have htop : IntermediateField.adjoin K {ζ} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic ζ),
      IntermediateField.top_toSubalgebra]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop' : IntermediateField.adjoin K (A : Set E) = ⊤ := by
    refine top_le_iff.mp (htop ▸ ?_)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin K (A : Set E) (IntermediateField.mem_adjoin_simple_self ℚ ζ)))
  have hfinA : Module.finrank ℚ A = m.totient := IsCyclotomicExtension.finrank A (cyclotomic.irreducible_rat hm.pos)
  have hfinE : Module.finrank K E = m.totient := by
    have h' : Module.finrank K (IntermediateField.adjoin K (A : Set E)) = m.totient := by
      rw [Module.finrank, hrk]
      exact hfinA
    rwa [htop', IntermediateField.finrank_top'] at h'
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hdeg : (minpoly K ζ).natDegree = m.totient := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hfinE]
  have hdvd : minpoly K ζ ∣ cyclotomic m K := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm.pos
  have heq : cyclotomic m K = minpoly K ζ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m K) hdvd
      (by rw [natDegree_cyclotomic, hdeg])
  rw [heq]
  exact minpoly.irreducible hint
end GlobalTheory
