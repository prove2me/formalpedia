-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.finPart_eq_one_of_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:02.98064+00:00
-- url     : https://prove2.me/submissions/4c920d2a-3cf4-4425-900d-bc7af9650d88

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_exists_cong
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_val_eq_one
import Theorems.Thm_Formalism_L2_Host_HChar_unrAt_iff
import Theorems.Thm_GlobalTheory_CMVal_Fibre_finPart_eq_one_of_fibres
import Theorems.Thm_GlobalTheory_CMVal_mem_hatOUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution {c : Ideal (OF E)} {χ : HChar E} (hF : TrivOnF χ)
    (hl : ∀ v : HeightOneSpectrum (OF E), ∃ n : ℕ, v.asIdeal ^ n ∣ c ∧ ∀ P, Over P v → LevelLe χ P n)
    {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) : finPart χ y = 1 := by
  refine Fibre.finPart_eq_one_of_fibres E χ y fun v => ?_
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hO : ∀ P ∈ S, Over P v := fun P hP => by
    rw [hS] at hP
    unfold Formalism.L2.Host.aboveF at hP
    rw [Set.Finite.mem_toFinset] at hP
    have : P.under (OF E) = v := hP
    rw [← this]; rfl
  obtain ⟨n, hn, hlev⟩ := hl v
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Finset.prod_eq_one fun P hP => (χ.unrAt_iff P).2 (hlev P (hO P hP)) _ (val_eq_one hy P)
  obtain ⟨a, ha⟩ := exists_cong v n hn S hO (mem_hatOUnits.1 hy).1
  have hva : ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P) = 1 := fun P hP => by
    have hlt : Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - (y : Af E) P) < Valued.v ((y : Af E) P) := by
      rw [val_eq_one hy P]
      refine (ha P hP).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, val_eq_one hy P]
  by_cases h0 : algebraMap (OF E) E a = 0
  · refine Finset.prod_eq_one fun P hP => ?_
    have h1 := hva P hP
    rw [h0, map_zero] at h1
    exact absurd (h1.symm.trans (map_zero _)) one_ne_zero
  let k' : (maximalRealSubfield E)ˣ := Units.mk0 (a : maximalRealSubfield E)
    (fun h1 => h0 (congrArg Subtype.val h1))
  have h2 := hF.1 v k'
  unfold Formalism.L2.Host.HChar.resFin at h2
  rw [MonoidHom.finsetProd_apply] at h2
  rw [← h2]
  refine Finset.prod_congr rfl fun P hP => ?_
  set u : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) k') with hu
  have hu' : (u : P.adicCompletion E) = algebraMap E (Af E) (algebraMap (OF E) E a) P := rfl
  have hvu : Valued.v (u : P.adicCompletion E) = 1 := hva P hP
  show χ.loc P (coord P y) = χ.loc P u
  have h3 : χ.loc P (u / coord P y) = 1 := by
    refine hlev P (hO P hP) _ ?_ ?_
    · show Valued.v ((u / coord P y : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, hvu, coe_coord, val_eq_one hy P, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one (coord P y).ne_zero, map_div₀, coe_coord, val_eq_one hy P, div_one, hu']
      exact ha P hP
  rw [map_div, div_eq_one] at h3
  exact h3.symm
end GlobalTheory.CMVal.OrderUnits
