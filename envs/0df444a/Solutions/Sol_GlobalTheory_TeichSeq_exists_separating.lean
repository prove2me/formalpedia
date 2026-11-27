-- Prove2me | solution 1 for GlobalTheory.TeichSeq.exists_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:53:25.98325+00:00
-- url     : https://prove2.me/submissions/4736f83e-4ebd-4396-96ce-5cc6c1021d21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
import Theorems.Thm_GlobalTheory_TeichSeq_frob_iter
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
open GlobalTheory GlobalTheory.TeichSeq
namespace GlobalTheory.TeichSeq
theorem _root_.solution {O k : Type} [CommRing O] [CommRing k] [IsDomain k] {d : ℕ} [NeZero d]
    (l : ℕ) (hl : 1 < l) (φ : ZMod d → (O →+* k)) (h : ∀ a x, φ (a + 1) x = φ a x ^ l)
    (hs : ∀ a a', a ≠ a' → ∃ x, φ a x ≠ φ a' x) :
    ∃ x, (∀ a, φ a x ≠ 0) ∧ Function.Injective (fun a => φ a x) := by
  classical
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl
  have hper : ∀ x, φ 0 x ^ l ^ d = φ 0 x := fun x => by
    rw [← frob_iter l φ h]; simp
  have hval : ∀ a x, φ a x = φ 0 x ^ l ^ a.val := fun a x => by
    rw [← frob_iter l φ h]; simp
  have hfin : ((φ 0).range : Set k).Finite := by
    have hne : (Polynomial.X ^ l ^ d - Polynomial.X : Polynomial k) ≠ 0 :=
      (Polynomial.monic_X_pow_sub (by
        rw [Polynomial.degree_X]; exact_mod_cast hq)).ne_zero
    refine (Polynomial.finite_setOf_isRoot hne).subset ?_
    rintro _ ⟨x, rfl⟩
    simp [hper]
  haveI : Finite (φ 0).range := hfin
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := ((φ 0).range)ˣ)
  obtain ⟨x, hx⟩ := (g : (φ 0).range).2
  have hx0 : φ 0 x ≠ 0 := by
    rw [hx]; intro h0
    exact g.ne_zero (Subtype.ext h0)
  refine ⟨x, fun a => by rw [hval]; exact pow_ne_zero _ hx0, fun a a' haa => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := hs a a' hne
  apply hy
  simp only at haa
  rw [hval a, hval a'] at haa ⊢
  by_cases hy0 : φ 0 y = 0
  · rw [hy0, zero_pow (by positivity), zero_pow (by positivity)]
  · have hu : IsUnit (⟨φ 0 y, y, rfl⟩ : (φ 0).range) :=
      ((Finite.isField_of_domain _).mul_inv_cancel
        (fun h0 => hy0 (congrArg Subtype.val h0))).elim fun b hb => IsUnit.of_mul_eq_one b hb
    obtain ⟨u, hu⟩ := hu
    obtain ⟨m, hm⟩ := hg u
    have : φ 0 y = φ 0 x ^ m := by
      rw [hx]
      have := congrArg (fun t : ((φ 0).range)ˣ => ((t : (φ 0).range) : k)) hm
      simp only [hu] at this
      simpa using this.symm
    rw [this, ← pow_mul, ← pow_mul, mul_comm m, mul_comm m, pow_mul, pow_mul, haa]
end GlobalTheory.TeichSeq
