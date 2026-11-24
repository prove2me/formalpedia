-- Prove2me | solution 1 for GlobalTheory.GluedOrbit.smul_gluedS_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:45:43.273478+00:00
-- url     : https://prove2.me/submissions/4ac9b922-1291-4b3f-b8ff-5f8cc126e081

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Theorems.Thm_GlobalTheory_GluedOrbit_eq_gluedS_of_mem
import Theorems.Thm_GlobalTheory_GluedOrbit_gluedS_zero_eq_lastPair_lat
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LevelUnfold_embX_smul_gluedS
import Theorems.Thm_GlobalTheory_LevelUnfold_gluedS_congr
import Theorems.Thm_GlobalTheory_LevelUnfold_oneOrbit
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
noncomputable section
open GlobalTheory GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
namespace GlobalTheory.GluedOrbit
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k),
    (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec →
    (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) →
    (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨
      h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨
    ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  intro k _ _ _ _ n _ _ q P h hz hq
  have hML : (h • gluedS q 1 P.ker P.vec).IsLattice k := inferInstance
  generalize h • gluedS q 1 P.ker P.vec = M at hz hq hML ⊢
  haveI := hML
  haveI : (interX M).IsLattice k := GlobalTheory.LevelUnfold.isLattice_interX M
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  by_cases hO : ∀ x ∈ M, x (Sum.inr 0) ∈ 𝒪[k]
  · refine Or.inl ⟨interX M, inferInstance, Or.inl ?_⟩
    ext y
    rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    constructor
    · intro hy
      refine ⟨?_, hO y hy⟩
      have e : inX k n 1 (y ∘ Sum.inl) = y - (⟨_, hO y hy⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hz)
    · rintro ⟨h1, h2⟩
      have e : y = inX k n 1 (y ∘ Sum.inl) + (⟨_, h2⟩ : 𝒪[k]) • (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · simp [inX]
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change y (Sum.inr 0) = 0 + y (Sum.inr 0) * (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          simp
      rw [e]
      exact add_mem h1 (M.smul_mem _ hz)
  · push_neg at hO
    obtain ⟨m₀, hm₀, hm₀'⟩ := hO
    have ht : IsUnit (⟨_, hq m₀ hm₀⟩ : 𝒪[k]) := by
      by_contra ht
      obtain ⟨s, hs⟩ := q.mem_max_iff.1 ((IsLocalRing.mem_maximalIdeal _).2 ht)
      apply hm₀'
      have h' : (q.1 : k) * m₀ (Sum.inr 0) = (q.1 : k) * s := congrArg Subtype.val hs
      rw [mul_left_cancel₀ q.ne_zero h']
      exact s.2
    obtain ⟨u, hu⟩ := ht
    have hu' : ((u : 𝒪[k]) : k) = (q.1 : k) * m₀ (Sum.inr 0) := congrArg Subtype.val hu
    have hinv : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * ((u : 𝒪[k]) : k) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      exact this
    set m : n ⊕ Fin 1 → k := ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • m₀
    have hm : m ∈ M := M.smul_mem _ hm₀
    have hm1 : m (Sum.inr 0) = q.inv := by
      change ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])) : k) * m₀ (Sum.inr 0) = (q.1 : k)⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hinv, hu']
      ring
    have hMeq := eq_gluedS_of_mem q hq hm hm1
    have hqf : q.1 • (m ∘ Sum.inl) ∈ interX M := by
      have e : inX k n 1 (q.1 • (m ∘ Sum.inl)) = q.1 • m - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) := by
        ext (j | j)
        · change (q.1 : k) * m (Sum.inl j) = (q.1 : k) * m (Sum.inl j) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inl j)
          simp
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = (q.1 : k) * m (Sum.inr 0) - (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) (Sum.inr 0)
          rw [hm1, hqi]
          simp
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem (M.smul_mem _ hm) hz
    by_cases hf : m ∘ Sum.inl ∈ interX M
    · refine Or.inl ⟨interX M, inferInstance, Or.inr ?_⟩
      calc M = gluedS q 1 (interX M) (m ∘ Sum.inl) := hMeq
        _ = gluedS q 1 (interX M) 0 := GlobalTheory.LevelUnfold.gluedS_congr (by simpa using hf)
        _ = (lastPair q (interX M)).lat := gluedS_zero_eq_lastPair_lat q _
    · refine Or.inr ?_
      have hG : IsGlue (interX M) (m ∘ Sum.inl) := (isGlue_iff q).2 ⟨inferInstance, hf, hqf⟩
      obtain ⟨g, hg1, hg2⟩ := (GlobalTheory.LevelUnfold.oneOrbit (k := k) (n := n) (c := 1) (q := q)).1 P.ker (interX M)
        P.vec (m ∘ Sum.inl) (Pair.isGlue P.hasVal_vec) hG
      refine ⟨g, ?_⟩
      rw [GlobalTheory.LevelUnfold.embX_smul_gluedS, hg1, GlobalTheory.LevelUnfold.gluedS_congr hg2]
      exact hMeq
end GlobalTheory.GluedOrbit
