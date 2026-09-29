-- Prove2me | solution 1 for GrothendieckTeichmuller.ihara_deriv_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T05:39:37.539027+00:00
-- url     : https://prove2.me/submissions/9e856185-7b1c-4a1d-b74a-93616e279e88

import Definitions.Def_GT_grt1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open GrothendieckTeichmuller

/-!
# The Ihara bracket of the two generators, and the commutator of Ihara derivations

Mathlib has neither the Grothendieck-Teichmuller Lie algebra nor the Ihara bracket; the
extensionality principle for derivations of a free Lie algebra is built here in a private
namespace.
-/

namespace IharaAux


theorem bracket_gx_gy : iharaBracket gx gy = 0 := by
  rw [iharaBracket, iharaDeriv_gy, iharaDeriv_gx, sub_zero, ← lie_skew, neg_add_cancel]

/-- The graph of a derivation, as a Lie algebra morphism into the semidirect product. -/
noncomputable def derivHom (D : LieDerivation ℚ Lxy Lxy) : Lxy →ₗ⁅ℚ⁆ AdExt where
  toFun u := ((⟨u, D u⟩ : Lxy × Lxy) : AdExt)
  map_add' u v := by
    refine AdExt.ext' rfl ?_
    exact map_add D u v
  map_smul' c u := by
    refine AdExt.ext' rfl ?_
    exact map_smul D c u
  map_lie' := by
    intro u v
    refine AdExt.ext' rfl ?_
    exact LieDerivation.apply_lie_eq_sub D u v

/-- Two derivations of the free Lie algebra on `x`, `y` agreeing on the generators are equal. -/
theorem deriv_ext {D E : LieDerivation ℚ Lxy Lxy} (hx : D gx = E gx) (hy : D gy = E gy) :
    D = E := by
  have h : derivHom D = derivHom E := by
    refine FreeLieAlgebra.hom_ext ?_
    intro i
    fin_cases i
    · exact AdExt.ext' rfl hx
    · exact AdExt.ext' rfl hy
  ext u
  exact congrArg (fun φ : Lxy →ₗ⁅ℚ⁆ AdExt => (AdExt.toPair (φ u)).2) h

theorem deriv_commutator (f g : Lxy) :
    ⁅iharaDeriv f, iharaDeriv g⁆ =
      iharaDeriv ⁅f, g⁆ + iharaDeriv (iharaDeriv f g) - iharaDeriv (iharaDeriv g f) := by
  refine deriv_ext ?_ ?_
  · rw [LieDerivation.commutator_apply, iharaDeriv_gx, iharaDeriv_gx]
    simp only [LieDerivation.sub_apply, LieDerivation.add_apply, iharaDeriv_gx, map_zero]
    abel
  · rw [LieDerivation.commutator_apply, iharaDeriv_gy, iharaDeriv_gy]
    rw [LieDerivation.apply_lie_eq_sub (iharaDeriv f) gy g,
      LieDerivation.apply_lie_eq_sub (iharaDeriv g) gy f,
      iharaDeriv_gy, iharaDeriv_gy]
    simp only [LieDerivation.sub_apply, LieDerivation.add_apply, iharaDeriv_gy]
    rw [leibniz_lie gy f g, ← lie_skew ⁅gy, f⁆ g]
    abel


end IharaAux

theorem solution (f g : GrothendieckTeichmuller.Lxy) :
    ⁅GrothendieckTeichmuller.iharaDeriv f, GrothendieckTeichmuller.iharaDeriv g⁆ =
      GrothendieckTeichmuller.iharaDeriv ⁅f, g⁆ +
        GrothendieckTeichmuller.iharaDeriv (GrothendieckTeichmuller.iharaDeriv f g) -
        GrothendieckTeichmuller.iharaDeriv (GrothendieckTeichmuller.iharaDeriv g f) :=
  IharaAux.deriv_commutator f g
