-- Prove2me | solution 1 for GlobalTheory.ResidueChar.exists_pow_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:21.66972+00:00
-- url     : https://prove2.me/submissions/c459ec81-a493-426b-ab0c-395c649f8fae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacter
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
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
theorem _root_.solution {K k : Type} [Field K] [Finite K] [CommRing k] [IsDomain k]
    (l : ℕ) [Fact l.Prime] [CharP K l] (f g : K →+* k) :
    ∃ j : ℕ, ∀ y, g y = f y ^ l ^ j := by
  classical
  have := Fintype.ofFinite K
  have hmem : ∀ y, g y ∈ f.range := fun y => by
    have h1 : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K) =
        ∏ a : K, (Polynomial.X - Polynomial.C a) := by
      have hm : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
        Polynomial.monic_X_pow_sub (by
          rw [Polynomial.degree_X]; exact_mod_cast Fintype.one_lt_card)
      have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by
        rw [FiniteField.roots_X_pow_card_sub_X,
          FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
        rfl)
      rw [← this, FiniteField.roots_X_pow_card_sub_X]
      rfl
    have h2 := congrArg (Polynomial.eval₂RingHom f (g y)) h1
    rw [map_prod] at h2
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] at h2
    rw [← map_pow, FiniteField.pow_card, sub_self] at h2
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h2.symm
    exact ⟨a, (sub_eq_zero.1 ha).symm⟩
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨f.rangeRestrict.injective, f.rangeRestrict_surjective⟩
  let s : K →+* K := e.symm.toRingHom.comp (g.codRestrict f.range hmem)
  have hs : ∀ y, f (s y) = g y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply (g.codRestrict f.range hmem y))
  let := ZMod.algebra K l
  let s' : K →ₐ[ZMod l] K := { s with
    commutes' := fun r => DFunLike.congr_fun
      (Subsingleton.elim (s.comp (algebraMap (ZMod l) K)) (algebraMap (ZMod l) K)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) K).2 s'
  refine ⟨j, fun y => ?_⟩
  have : s y = y ^ l ^ (j : ℕ) := by
    have h := DFunLike.congr_fun hj y
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card] at h
    exact h.symm
  rw [← hs, this, map_pow]
end GlobalTheory.ResidueChar
