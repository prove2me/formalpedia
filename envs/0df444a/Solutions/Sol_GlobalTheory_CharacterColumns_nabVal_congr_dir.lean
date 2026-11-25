-- Prove2me | solution 1 for GlobalTheory.CharacterColumns.nabVal_congr_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:14:04.739381+00:00
-- url     : https://prove2.me/submissions/15d50e30-25dc-43b7-bf41-11e3661e7ac2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ConstantCoeffDmonOfEigen
import Theorems.Thm_GlobalTheory_CharacterColumns_dmonOf_congr_dir
import Theorems.Thm_GlobalTheory_PullbackColumn_dpolyOf_monomial_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CharacterColumns
namespace GlobalTheory.CharacterColumns
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (w0 : O)
    (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι] (u u' : ι → Fin d → k) (mo : ι →₀ ℕ)
    (hu : ∀ l, mo l ≠ 0 → u l = u' l) :
    B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) =
      B.nabVal k h w0 m f u' (MvPolynomial.monomial mo 1) := by
  unfold FB.nabVal
  rw [PullbackColumn.dpolyOf_monomial_one, PullbackColumn.dpolyOf_monomial_one,
    dmonOf_congr_dir _ u u' mo hu]
end GlobalTheory.CharacterColumns
