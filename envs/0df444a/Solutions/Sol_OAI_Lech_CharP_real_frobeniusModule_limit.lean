-- Prove2me | solution 1 for OAI.Lech.CharP.real_frobeniusModule_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:00:00.454873+00:00
-- url     : https://prove2.me/submissions/49b847d9-a4ad-4bdf-97b1-c2d196a43e3e

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L004
import Theorems.Thm_OAI_Lech_frobeniusModule_finiteLength

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaPerfectResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (IsLocalRing.ResidueField D) p]

omit [IsDomain D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  [PerfectRing (IsLocalRing.ResidueField D) p] in
lemma real_frobeniusModule_limit_oai (M : ModuleCat.{u} D) (hM : IsFiniteLength D M)
    (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*dimension D))⁻¹ *
      (Module.length D (FrobeniusModule D p n M)).toENNReal) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ((Module.length D (FrobeniusModule D p n M)).toNat : ℝ) /
      ((p:ℝ)^n)^dimension D) atTop (𝓝 L.toReal) := by
  apply ((ENNReal.tendsto_toReal hL).comp hlim).congr
  intro n
  have hn : Module.length D (FrobeniusModule D p n M) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (frobeniusModule_finiteLength D p M hM n)
  simp only [Function.comp_apply,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_natCast]
  rw [← ENat.natCast_toNat hn,ENat.toENNReal_coe,ENNReal.toReal_natCast]
  rw [pow_mul,div_eq_mul_inv,mul_comm]
  simp only [ENat.toNat_natCast]

end Lech.CharP

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.CharP.real_frobeniusModule_limit_oai.{u} := @OAI.Lech.CharP.real_frobeniusModule_limit_oai.{u}
