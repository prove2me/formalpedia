-- Prove2me | solution 1 for GlobalTheory.HL.Glue.local_le_lat_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:52.428155+00:00
-- url     : https://prove2.me/submissions/2014d08b-ed4e-475d-9a52-b1acb6f5da8c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalLatticeLeCompletionGluedLattice
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Glue
namespace GlobalTheory.HL.Glue
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p)
    (hN : ∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) :
    ∀ p, Λ p ≤ A.lat p Γ := by
  intro p v hv
  have hsingle : ∀ i : Fin n, ((N : E) • (Pi.single i 1 : Fin n → E)) ∈ Γ := by
    intro i
    rw [hΓ]
    intro q
    have h1 : A.bc q ((N : E) • (Pi.single i 1 : Fin n → E)) =
        (N : (A.loc q).Ep) • (Pi.single i 1 : Fin n → (A.loc q).Ep) := by
      funext j
      simp only [Places.bc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h1]
    apply hN
    intro j
    by_cases h : j = i
    · subst h; simp [Subring.one_mem]
    · simp [Pi.single_apply, h, Subring.zero_mem]
  have hint : ∀ w : Fin n → (A.loc p).Ep, (∀ i, w i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • w ∈ A.lat p Γ := by
    intro w hw
    have hw' : (N : (A.loc p).Ep) • w =
        ∑ i, (⟨w i, hw i⟩ : (A.L p).O) • A.bc p ((N : E) • (Pi.single i 1 : Fin n → E)) := by
      funext j
      simp [Places.bc, Subring.smul_def, Pi.single_apply, Finset.sum_apply, mul_comm]
      simp [apply_ite (A.loc p).ιE, mul_ite, Finset.sum_ite_eq, mul_comm]
    rw [hw']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle i, rfl⟩)
  have hfin : ∀ i, {q | (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q ∉ (A.L q).O}.Finite := by
    intro i
    apply (Set.finite_singleton p).subset
    intro q hq
    by_contra h
    apply hq
    rw [Pi.single_eq_of_ne h]
    exact (A.L q).O.zero_mem
  choose x hx using fun i => happ _ (hfin i)
  choose o ho hxo using hx
  have hbc : ∀ q, A.bc q (fun i => x i) =
      (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) + (N : (A.loc q).Ep) • (fun i => o i q) := by
    intro q
    funext i
    have h2 := hxo i q
    simp only [Places.bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h2]
    ring
  have hX : (fun i => x i) ∈ Γ := by
    rw [hΓ]
    intro q
    rw [hbc q]
    refine (Λ q).add_mem ?_ (hN q _ fun i => ho i q)
    by_cases hq : q = p
    · subst hq
      simpa using hv
    · have h3 : (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) = 0 := by
        funext i
        simp [Pi.single_eq_of_ne hq]
      rw [h3]
      exact (Λ q).zero_mem
  have hv' : v = A.bc p (fun i => x i) - (N : (A.loc p).Ep) • (fun i => o i p) := by
    rw [hbc p]
    funext i
    simp
  rw [hv']
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, hX, rfl⟩) (hint _ fun i => ho i p)
end GlobalTheory.HL.Glue
