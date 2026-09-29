-- Prove2me | solution 1 for ModularCurve.exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6caff746-7beb-52cc-95ec-188b8f18d3a8

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ.ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "modularFunctionFieldBar qExpand jq jq_mem jqd_mem_full modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.derivative_X_sub_X_pow_sq (k : Type*) [CommRing k] (p : ℕ) [CharP k p] :
    Polynomial.derivative (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k) = 1 := by
  rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_X_pow]
  have : ((p ^ 2 : ℕ) : k) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero k p, zero_pow two_ne_zero]
  rw [this, map_zero, zero_mul, sub_zero]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.rootMultiplicity_X_sub_X_pow_sq_eq_one (k : Type*) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (b : k) (hb : b ^ (p ^ 2) = b) :
    (Polynomial.X - Polynomial.X ^ (p ^ 2) : Polynomial k).rootMultiplicity b = 1 := by
  set Q : Polynomial k := Polynomial.X - Polynomial.X ^ (p ^ 2) with hQ
  have hp : p.Prime := Fact.out
  have hQ0 : Q ≠ 0 := by
    intro h
    have h' : (Polynomial.X : Polynomial k) = Polynomial.X ^ (p ^ 2) := sub_eq_zero.mp h
    have hdeg := congrArg Polynomial.natDegree h'
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at hdeg
    have h1 : p ^ 2 = 1 := hdeg.symm
    rcases pow_eq_one_iff.mp h1 with h1 | h1
    · exact hp.one_lt.ne' h1
    · exact two_ne_zero h1
  have hroot : Q.IsRoot b := by
    simp only [hQ, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, hb,
      sub_self]
  have hge : 1 ≤ Q.rootMultiplicity b := (Polynomial.rootMultiplicity_pos hQ0).mpr hroot
  have hle : Q.rootMultiplicity b ≤ 1 := by
    by_contra hlt
    have hlt' : 1 < Q.rootMultiplicity b := not_le.mp hlt
    have hder := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt'
    rw [Function.iterate_one, hQ, ModularCurve.derivative_X_sub_X_pow_sq k p] at hder
    simp at hder
  omega

theorem solution
    (p : ℕ) [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (C : ComponentChart A ↥(modularFunctionFieldBar p) Fbar)
    (X : Fbar) (xpl : IsLocalRing.ResidueField ↥A → Place (IsLocalRing.ResidueField ↥A) Fbar)
    (hord_poly : ∀ (c : IsLocalRing.ResidueField ↥A) (P : Polynomial (IsLocalRing.ResidueField ↥A)),
      (xpl c).ord (Polynomial.aeval X P) = (P.rootMultiplicity c : ℤ))
    (hjF : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ∈ C.integers)
    (hjpF : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ : modularFunctionFieldBar p) ∈ C.integers)
    (hres_jp : C.residue ⟨_, hjpF⟩ = X) (hres_j : C.residue ⟨_, hjF⟩ = X ^ p)
    (a : IsLocalRing.ResidueField ↥A) (ha2 : a ^ (p ^ 2) = a) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full p (dvd_refl p))⟩ : modularFunctionFieldBar p)
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full p (jq_mem p))⟩ : modularFunctionFieldBar p) ^ p
        ∈ C.integers,
      (xpl (a ^ p)).ord (C.residue ⟨_, h⟩) = 1 := by
  set jF : ↥(modularFunctionFieldBar p) := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full p (jq_mem p))⟩ with hjF_def
  set jpF : ↥(modularFunctionFieldBar p) := ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full p (dvd_refl p))⟩ with hjpF_def
  have hG : jpF - jF ^ p ∈ C.integers := sub_mem hjpF (pow_mem hjF p)
  refine ⟨hG, ?_⟩
  have hres : C.residue ⟨jpF - jF ^ p, hG⟩ = X - X ^ (p ^ 2) := by
    have hsplit : (⟨jpF - jF ^ p, hG⟩ : C.integers) = ⟨jpF, hjpF⟩ - ⟨jF, hjF⟩ ^ p := rfl
    rw [hsplit, map_sub, map_pow, hres_jp, hres_j, ← pow_mul, ← sq]
  have hpoly : X - X ^ (p ^ 2)
      = Polynomial.aeval X (Polynomial.X - Polynomial.X ^ (p ^ 2) :
          Polynomial (IsLocalRing.ResidueField ↥A)) := by
    simp only [map_sub, map_pow, Polynomial.aeval_X]
  have hap : (a ^ p) ^ (p ^ 2) = a ^ p := by
    rw [← pow_mul, mul_comm, pow_mul, ha2]
  rw [hres, hpoly, hord_poly,
    ModularCurve.rootMultiplicity_X_sub_X_pow_sq_eq_one (IsLocalRing.ResidueField ↥A) p (a ^ p) hap]
  rfl

end S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ
end P2MW
export P2MW.S_ModularCurve_exists_nodeCoord_mem_integers_ord_residue_eq_one_zeroChart_univ (solution)
