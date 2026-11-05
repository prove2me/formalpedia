-- Prove2me | solution 1 for OAI.SharpPlanar.hexNat_residue_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:05:56.001076+00:00
-- url     : https://prove2.me/submissions/b003c724-5a38-4fdd-8d11-a78b2cac2f77

import Mathlib
import Definitions.Def_OAIQ098E000
import Definitions.Def_OAIQ098E013

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma hexForm_nonneg (v : ℤ×ℤ) : 0 ≤ hexForm v := by
  unfold hexForm
  nlinarith [sq_nonneg (2*v.1+v.2),sq_nonneg v.2]
lemma hexNat_coe (v : ℤ×ℤ) : (hexNat v:ℤ)=hexForm v := Int.toNat_of_nonneg (hexForm_nonneg v)
lemma hexResidue_table : ∀ a c : Fin 12,
    (a.val^2+a.val*c.val+c.val^2)%12 ∈ residues := by decide +kernel
lemma hexNat_residue_e_oai (v : ℤ×ℤ) : hexNat v%12∈residues := by
  have ha : 0 ≤ v.1%12 := Int.emod_nonneg _ (by norm_num)
  have hc : 0 ≤ v.2%12 := Int.emod_nonneg _ (by norm_num)
  have ha' : (v.1%12).toNat<12 := by omega
  have hc' : (v.2%12).toNat<12 := by omega
  have hh := hexResidue_table ⟨(v.1%12).toNat,ha'⟩ ⟨(v.2%12).toNat,hc'⟩
  have he : (hexNat v:ℤ)%12=((v.1%12).toNat^2+(v.1%12).toNat*(v.2%12).toNat+(v.2%12).toNat^2:ℕ)%12 := by
    rw [hexNat_coe]
    push_cast
    rw [Int.toNat_of_nonneg ha,Int.toNat_of_nonneg hc]
    simp only [hexForm,pow_two,Int.add_emod,Int.mul_emod,Int.emod_emod]
  have he' : hexNat v%12=((v.1%12).toNat^2+(v.1%12).toNat*(v.2%12).toNat+(v.2%12).toNat^2)%12 := by exact_mod_cast he
  rw [he']; exact hh
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.hexNat_residue_e_oai := @OAI.SharpPlanar.hexNat_residue_e_oai
