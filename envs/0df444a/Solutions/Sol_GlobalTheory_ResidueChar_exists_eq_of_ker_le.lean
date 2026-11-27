-- Prove2me | solution 1 for GlobalTheory.ResidueChar.exists_eq_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:53:19.821671+00:00
-- url     : https://prove2.me/submissions/7e17cef2-ae3d-4dfc-afbd-a53a8640f00d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacter
import Theorems.Thm_GlobalTheory_ResidueChar_exists_pow_of_finite_field
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_TeichSeq_frob_iter
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ResidueChar
namespace GlobalTheory.ResidueChar
theorem _root_.solution {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) [Fact l.Prime] [CharP k l] (φ : ZMod d → (O →+* k))
    (h : ∀ a x, φ (a + 1) x = φ a x ^ l) (g : O →+* k) (hg : ∀ x, φ 0 x = 0 → g x = 0) :
    ∃ a, ∀ x, g x = φ a x := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← TeichSeq.frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  have : Finite (φ 0).range := hfin
  let : Field (φ 0).range := (Finite.isField_of_domain _).toField
  let g' : (φ 0).range →+* k :=
    (φ 0).rangeRestrict.liftOfSurjective (φ 0).rangeRestrict_surjective
      ⟨g, fun x hx => hg x (congrArg Subtype.val (RingHom.mem_ker.1 hx))⟩
  have hg' : ∀ x, g' ((φ 0).rangeRestrict x) = g x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  obtain ⟨j, hj⟩ := exists_pow_of_finite_field l (φ 0).range.subtype g'
  refine ⟨0 + (j : ZMod d), fun x => ?_⟩
  rw [TeichSeq.frob_iter l φ h, ← hg', hj]
  rfl
end GlobalTheory.ResidueChar
