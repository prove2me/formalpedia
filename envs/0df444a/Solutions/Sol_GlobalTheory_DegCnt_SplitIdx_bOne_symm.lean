-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.bOne_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:56.223794+00:00
-- url     : https://prove2.me/submissions/7c2826e2-d608-45fd-a3f4-b8aff4303f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_exists_mul
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_isLattice_field
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_idx_scal
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_Xa_mono
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_e_mem
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_level_lt
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_mem_of_level
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_mem_lead
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_step
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_mono
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_mul
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_idx_sup
import Theorems.Thm_GlobalTheory_IsSaturatedSubmodule_smul_mem_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (H : HermSpace K V) {r : ℕ} (N : NF H r) (hS : NFShape N.F N.F' N.j N.c)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hF : IsFrame N.F Λ N.aa) (hF' : IsFrame N.F' Λ N.aa) :
    bOne N.F' N.F Λ N.j = bOne N.F N.F' Λ N.j := by
  obtain ⟨hc0, -, hlev, -⟩ := hS
  set J := Λ ⊓ rs (𝓞 K) (II N.F N.F') with hJ
  have hX : ∀ x ∈ II N.F N.F', ∀ a, x ∈ N.F.Xa a ↔ x ∈ N.F'.Xa a := by
    intro x hx a
    by_cases h0 : x = 0
    · simp [h0]
    obtain ⟨b, al, al', h1, h2, -⟩ := hlev x hx h0
    exact ⟨fun h => mem_of_level _ h2 (level_lt _ h1 h), fun h => mem_of_level _ h1 (level_lt _ h2 h)⟩
  have one : ∀ a : Fin r, N.j ≤ a.val → idx (lead N.F' Λ a.castSucc) (lead N.F' J a.castSucc) =
      idx (lead N.F Λ a.castSucc) (lead N.F J a.castSucc) := by
    intro a ha
    have he : N.F'.e a.castSucc = N.c • N.F.e a.castSucc := N.same _ ha
    have hI : N.F.e a.castSucc ∈ II N.F N.F' := ⟨e_mem _ a.2, by
      have := e_mem N.F' a.2
      rwa [he, Submodule.smul_mem_iff _ hc0] at this⟩
    have l1 : lead N.F J a.castSucc ≤ N.aa a := hF.1 a ▸ Submodule.comap_mono (sup_le_sup_right inf_le_left _)
    have l2 : lead N.F' J a.castSucc ≤ N.aa a := hF'.1 a ▸ Submodule.comap_mono (sup_le_sup_right inf_le_left _)
    have hfg : (N.aa a).FG := (isNoetherian_submodule.1 (FractionalIdeal.isNoetherian _)) _ le_rfl
    have hm : ∀ t, t ∈ lead N.F' J a.castSucc ↔ t * N.c ∈ lead N.F J a.castSucc := fun t => by
      rw [mem_lead, mem_lead, he, smul_smul]
      refine exists_congr fun x => and_congr_right fun hx => (hX _ ?_ _).symm
      exact Submodule.sub_mem _ hx.2 (Submodule.smul_mem _ _ hI)
    obtain ⟨n, hn, h⟩ := exists_mul hΛ (N.F.e a.castSucc)
    have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
    have m1 : (n : K) ∈ lead N.F J a.castSucc :=
      (mem_lead _ _ _ _).2 ⟨_, ⟨h, Submodule.smul_mem _ _ hI⟩, by simp⟩
    have m2 : (n : K) * N.c⁻¹ ∈ lead N.F' J a.castSucc := by
      rw [hm]; simpa [hc0] using m1
    rw [hF.1, hF'.1]
    exact idx_scal N.c_norm (isLattice_field hfg (l1 m1) hn') (isLattice_field (hfg.of_le l1) m1 hn')
      (isLattice_field (hfg.of_le l2) m2 (mul_ne_zero hn' (inv_ne_zero hc0))) hm l1 l2
  have mono : ∀ (F : FlagD H r) {a b : ℕ}, a ≤ b → latF F Λ a ⊔ J ≤ latF F Λ b ⊔ J := fun F a b h =>
    sup_le_sup_right (inf_le_inf_left _ (fun x hx => Xa_mono F h hx)) _
  have all : ∀ m, N.j ≤ m → m ≤ r → idx (latF N.F' Λ m ⊔ J) (latF N.F' Λ N.j ⊔ J) =
      idx (latF N.F Λ m ⊔ J) (latF N.F Λ N.j ⊔ J) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; simp [idx]
    | succ m hm ih =>
      intro h
      rw [← idx_mul (mono N.F' hm) (mono N.F' (Nat.le_succ m)), ← idx_mul (mono N.F hm) (mono N.F (Nat.le_succ m)),
        ih (Nat.le_of_succ_le h)]
      congr 1
      exact (step N.F' inf_le_left ⟨m, h⟩).trans ((one ⟨m, h⟩ hm).trans (step N.F inf_le_left ⟨m, h⟩).symm)
  have := all r N.j_le le_rfl
  rw [idx_sup le_sup_right, idx_sup le_sup_right] at this
  rw [bOne, bOne, show II N.F' N.F = II N.F N.F' from inf_comm _ _]
  exact this
end GlobalTheory.DegCnt.SplitIdx
