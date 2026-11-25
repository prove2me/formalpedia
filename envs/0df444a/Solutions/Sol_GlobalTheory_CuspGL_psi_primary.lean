-- Prove2me | solution 1 for GlobalTheory.CuspGL.psi_primary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:06.743404+00:00
-- url     : https://prove2.me/submissions/dd496a1c-3c9e-4160-939c-2cd72760c3be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyBlockAndInvariantUnderStabilizerNilradic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumMobiusInverseCharpolyInvariantLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSurjectivePiAdjoinRootKerEqRangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantSubspaceMobiusInverseCharpolyPrimaryEq
import Theorems.Thm_GlobalTheory_CuspGL_Primary_finrank_comap_of_surjective
import Theorems.Thm_GlobalTheory_CuspGL_Primary_additive_restrict
import Theorems.Thm_GlobalTheory_CuspGL_Primary_eq_top_of_nilpotent
import Theorems.Thm_GlobalTheory_CuspGL_Primary_aeval_mem
import Theorems.Thm_GlobalTheory_CuspGL_Primary_mem_image_of_mem_span
import Theorems.Thm_GlobalTheory_CuspGL_finsum_psi_le
import Theorems.Thm_GlobalTheory_CuspGL_psi_conj
import Theorems.Thm_GlobalTheory_T_mobiusInversion_affine_finrank_subspaces
import Theorems.Thm_P2M_GlobalTheory_T_exists_surjective_pi_adjoinRoot_ker_eq_range__b115a80cc821


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
open Primary
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by
  intro F _ _ V _ _ _ s hs g f m t hf hi hm hc ht
  classical
  haveI : Fact (Irreducible f) := ⟨hi⟩
  have he : 0 < f.natDegree := hi.natDegree_pos
  have he' : (f.natDegree : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  obtain ⟨t', π, hsurj, hπ, hker, ht'⟩ := GlobalTheory.T.exists_surjective_pi_adjoinRoot_ker_eq_range' F V g f
  obtain rfl : t' = t := Nat.eq_of_mul_eq_mul_left he (ht'.symm.trans ht)
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  have hK : Module.finrank F (AdjoinRoot f) = f.natDegree := (AdjoinRoot.powerBasis hi.ne_zero).finrank
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have hcard : Nat.card (AdjoinRoot f) = Nat.card F ^ f.natDegree := by
    rw [← hK]; exact Module.natCard_eq_pow_finrank
  have hN : (aeval g f) ^ m = 0 := by rw [← map_pow, ← hc, LinearMap.aeval_self_charpoly]
  have nak : ∀ W : Submodule F V, (∀ x ∈ W, g x ∈ W) →
      Submodule.span (AdjoinRoot f) (π '' W) = ⊤ → W = ⊤ := by
    intro W hW h
    refine eq_top_of_nilpotent (aeval g f) hN W (aeval_mem g W hW f) fun v => ?_
    obtain ⟨w, hw, hw'⟩ := mem_image_of_mem_span g f π hπ W hW (π v) (h ▸ Submodule.mem_top)
    have : v - w ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_sub, hw', sub_self]
    rw [hker] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨w, hw, u, by rw [hu]; abel⟩
  have htpos : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with rfl | h
    · exfalso
      have h1 := nak ⊥ (by simp) (Subsingleton.elim _ _)
      have h2 := LinearMap.charpoly_natDegree g
      rw [hc, hf.natDegree_pow, ← finrank_top, ← h1, finrank_bot] at h2
      exact (Nat.mul_pos hm he).ne' h2
    · exact h
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f)) :=
    Finite.of_injective _ SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F V)
  letI := Fintype.ofFinite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f))
  let P : Submodule F V → ℂ := fun W => if h : ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h) else 0
  let Φ : Submodule F V → Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) :=
    fun W => Submodule.span (AdjoinRoot f) (π '' W)
  let G : Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) → ℂ :=
    fun B => ∑ W ∈ Finset.univ.filter (fun W => Φ W = B), P W
  have hrk : Module.finrank (AdjoinRoot f) (Fin t' → AdjoinRoot f) = t' := by simp
  have main := GlobalTheory.T.mobiusInversion_affine_finrank_subspaces (AdjoinRoot f) (Fin t' → AdjoinRoot f) G
    ((Module.finrank F (LinearMap.ker π) : ℂ) * s f / f.natDegree) (s f) (by rw [hrk]; exact htpos) (by
      intro A
      have hA : ∀ x ∈ (A.restrictScalars F).comap π, g x ∈ (A.restrictScalars F).comap π := by
        intro x hx
        rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hx ⊢
        rw [hπ]; exact A.smul_mem _ hx
      have hle : ∀ W, Φ W ≤ A ↔ W ≤ (A.restrictScalars F).comap π := fun W => by
        rw [Submodule.span_le, Set.image_subset_iff]; rfl
      have h1 := finsum_psi_le F V s _ g hA
      have h2 := additive_restrict hs hf hi hc _ hA
      rw [finrank_comap_of_surjective π hsurj] at h2
      have h3 : Module.finrank F (A.restrictScalars F) = f.natDegree * Module.finrank (AdjoinRoot f) A := by
        rw [← hK, Module.finrank_mul_finrank]; rfl
      rw [h3] at h2
      have h4 : ∑ᶠ B : {B // B ≤ A}, G B.1 =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        rw [finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter (fun B => B ≤ A)) (by simp) G,
          Finset.sum_fiberwise_eq_sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext W; simp [hle]
      have h5 : ∑ᶠ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        have : ∀ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) = P W.1 := fun W => by simp only [P]; rw [dif_pos W.2.2]
        rw [finsum_congr this, finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter
            (fun W => W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W)) (by simp) P]
        refine Finset.sum_subset (fun W => by simp; tauto) fun W hW hW' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW hW'
        exact dif_neg fun h => hW' ⟨hW, h⟩
      rw [h4, ← h5, h1]
      push_cast at h2
      field_simp
      linear_combination h2)
  have hG : G ⊤ = psi s V g := by
    have htop : ∀ x ∈ (⊤ : Submodule F V), g x ∈ (⊤ : Submodule F V) := fun _ _ => trivial
    have h1 : G ⊤ = P ⊤ := by
      refine Finset.sum_eq_single_of_mem ⊤ ?_ fun W hW hW' => ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Φ]
        rw [Submodule.top_coe, Set.image_univ, hsurj.range_eq, Submodule.span_univ]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
        exact dif_neg fun h => hW' (nak W h hW)
    rw [h1]
    simp only [P]
    rw [dif_pos htop, ← psi_conj F s _ _ Submodule.topEquiv]
    congr 1
  rw [← hG, main, hrk, hcard]
  simp only [Nat.cast_pow, ← pow_mul]
end GlobalTheory.CuspGL
