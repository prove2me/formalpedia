-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.irreducible_map_adjoin_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/52fcbc8a-7bb4-5627-bbcb-01a4c8aac02e

import Mathlib
import Definitions.Def_ModularCurve_ModularEquationQ
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
import Theorems.Thm_ModularCurve_StarBank_starBank
import Theorems.Thm_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_irreducible_map_adjoin_jqNModC
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve IntermediateField in
theorem solution
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (data : ModularCurve.ModularPolynomialData M)
    (hM : (M : K) ≠ 0) :
    Irreducible (data.toJqNField K) := by
  classical

  set Jq : IntermediateField K (LaurentSeries K) :=
    IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hJq
  let jg : Jq := ⟨jqModC K, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  set Pq : Polynomial Jq := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Jq) jg) with hPq

  have hint : IsIntegral Jq (jqNModC K M) := isIntegral_jqNModC_of_modularPolynomialData K data
  have haeval : Polynomial.aeval (jqNModC K M) Pq = 0 := by
    rw [Polynomial.aeval_def, hPq, Polynomial.eval₂_map]
    have hcomp : (algebraMap Jq (LaurentSeries K)).comp (Polynomial.eval₂RingHom (Int.castRingHom Jq) jg) =
        (Polynomial.aeval (R := ℤ) (jqNModC K 1)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      show algebraMap Jq (LaurentSeries K) (Polynomial.eval₂ (Int.castRingHom Jq) jg Polynomial.X) =
        Polynomial.aeval (jqNModC K 1) (Polynomial.X : Polynomial ℤ)
      rw [Polynomial.eval₂_X, Polynomial.aeval_X, jqNModC_one]
      rfl
    rw [hcomp]
    have h := data.eval_jqNModC_mul_eq_zero K 1
    convert h using 3
    simp
  have hbase : ∀ (p : ℕ) [Fact p.Prime], p ∣ M → jqNModC K p ∉ Jq := by
    intro p hp hpM
    obtain ⟨r, hr⟩ := CharP.exists K
    rcases CharP.char_is_prime_or_zero K r with hrp | hr0
    · haveI : Fact r.Prime := ⟨hrp⟩
      have hpr : p ≠ r := by
        rintro rfl
        apply hM
        obtain ⟨c, rfl⟩ := hpM
        rw [Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul]
      exact StarBank.starBank (K := K) (ℓ := r) hpr
    · subst hr0
      haveI : CharZero K := CharP.charP_to_charZero K
      exact jqNModC_prime_not_mem_adjoin_of_charZero p
  have hfin := finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket (K := K) M hbase
  have hdegmin : (minpoly Jq (jqNModC K M)).natDegree = dedekindPsi M := by
    rw [← IntermediateField.adjoin.finrank hint, ← hfin]
  have hmin : Pq = minpoly Jq (jqNModC K M) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (data.monic.map _)
      (minpoly.dvd Jq _ haeval)
      (by rw [hPq, data.monic.natDegree_map, data.natDegree_eq, hdegmin])
  have hirrq : Irreducible Pq := hmin ▸ minpoly.irreducible hint

  let f : LaurentSeries K →ₐ[K] LaurentSeries K := qExpandAlgHomC K M
  have hmapJ : Jq.map f = jqNField K M := by
    rw [hJq, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : Jq ≃ₐ[K] jqNField K M :=
    (IntermediateField.equivMap Jq f).trans (IntermediateField.equivOfEq hmapJ)
  have he : ∀ x : Jq, ((e x : jqNField K M) : LaurentSeries K) = f x := fun x => by
    show (((IntermediateField.equivOfEq hmapJ) (IntermediateField.equivMap Jq f x) : jqNField K M) :
      LaurentSeries K) = f x
    rw [← IntermediateField.coe_equivMap_apply Jq f x]
    rfl
  have hPe : Polynomial.mapEquiv e.toRingEquiv Pq = data.toJqNField K := by
    rw [Polynomial.mapEquiv_apply, hPq, Polynomial.map_map]
    show _ = data.Φ.map _
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.eval₂_X]
    apply Subtype.ext
    show ((e jg : jqNField K M) : LaurentSeries K) = jqNModC K M
    rw [he]
    rfl
  rw [← hPe]
  exact hirrq.map (Polynomial.mapEquiv e.toRingEquiv)

end S_ModularCurve_ModularPolynomialData_irreducible_map_adjoin_jqNModC
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_irreducible_map_adjoin_jqNModC (solution)
