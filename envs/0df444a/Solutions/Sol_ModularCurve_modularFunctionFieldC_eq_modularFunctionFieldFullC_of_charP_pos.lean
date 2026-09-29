-- Prove2me | solution 1 for ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/cb46b34b-502d-5130-979f-2a6e6b43400f

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket
import Theorems.Thm_ModularCurve_StarBank_starBank
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve IntermediateField

namespace IgSol

theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    rw [Finset.mem_filter]; exact ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at this
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) this

theorem finrank_full (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (hJF : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ modularFunctionFieldFullC K N) :
    Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (extendScalars hJF) = dedekindPsi N := by
  have h8 : Module.finrank
      (IntermediateField.adjoin K ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N)))
      (modularFunctionFieldFullC K N) = dedekindPsi N :=
    finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

  have hlift : IntermediateField.lift
      (IntermediateField.adjoin K ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N)))
      = IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
    IntermediateField.lift_adjoin_simple K (modularFunctionFieldFullC K N) ⟨jqModC K, jqModC_mem_full K N⟩

  let i : IntermediateField.adjoin K ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N))
      ≃+* IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) :=
    { toFun := fun x => ⟨(x : modularFunctionFieldFullC K N), by
        rw [← hlift]; exact (IntermediateField.mem_lift (x : modularFunctionFieldFullC K N)).mpr x.2⟩
      invFun := fun y => ⟨⟨(y : LaurentSeries K), hJF y.2⟩, by
        have hy : (y : LaurentSeries K) ∈ IntermediateField.lift
            (IntermediateField.adjoin K ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N))) := by
          rw [hlift]; exact y.2
        exact (IntermediateField.mem_lift (⟨(y : LaurentSeries K), hJF y.2⟩ : modularFunctionFieldFullC K N)).mp hy⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let j : modularFunctionFieldFullC K N ≃+* extendScalars hJF :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  rw [← h8]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext x : 1
  rfl

end IgSol

open IgSol ModularCurve IntermediateField in
theorem solution
    (K : Type*) [Field K] (ℓ : ℕ) [CharP K ℓ] [NeZero ℓ] (N : ℕ) [NeZero N] (hlN : ¬ ℓ ∣ N) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N := by
  classical
  haveI : Fact ℓ.Prime := ⟨(CharP.char_is_prime_or_zero K ℓ).resolve_right (NeZero.ne ℓ)⟩
  have hN : (N : K) ≠ 0 := fun h => hlN ((CharP.cast_eq_zero_iff K ℓ N).mp h)

  have hsock : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ N →
      jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
    intro p hp hpN
    have hpℓ : p ≠ ℓ := fun h => hlN (h ▸ hpN)
    exact StarBank.starBank (K := K) (ℓ := ℓ) hpℓ

  have hJC : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ modularFunctionFieldC K N := by
    rw [IntermediateField.adjoin_le_iff]; rintro _ rfl; exact jqModC_mem K N
  have hJF : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ modularFunctionFieldFullC K N :=
    hJC.trans (modularFunctionFieldC_le_full K N)

  have hC : extendScalars hJC
      = IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K N} : Set (LaurentSeries K)) := by
    have e := IntermediateField.extendScalars_adjoin
      (K := IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (S := ({jqModC K, jqNModC K N} : Set (LaurentSeries K))) hJC
    refine e.trans ?_
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      ·
        have : (jqModC K : LaurentSeries K)
            = algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K)
                ⟨jqModC K, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩ := rfl
        rw [this]
        exact IntermediateField.algebraMap_mem _ _
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
  have hdegC : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (extendScalars hJC) = dedekindPsi N := by
    rw [hC]
    exact finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket (K := K) N hsock
  have hdegF := finrank_full K N hN hJF
  haveI : FiniteDimensional (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (extendScalars hJF) :=
    FiniteDimensional.of_finrank_pos (by rw [hdegF]; exact dedekindPsi_pos N)
  have heq : extendScalars hJC = extendScalars hJF :=
    IntermediateField.eq_of_le_of_finrank_eq
      ((IntermediateField.extendScalars_le_extendScalars_iff hJC hJF).mpr (modularFunctionFieldC_le_full K N))
      (by rw [hdegC, hdegF])
  have hcoe := congrArg (fun X : IntermediateField (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K) =>
    (X : Set (LaurentSeries K))) heq
  simp only [IntermediateField.coe_extendScalars] at hcoe
  exact SetLike.coe_injective hcoe

end S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos (solution)
