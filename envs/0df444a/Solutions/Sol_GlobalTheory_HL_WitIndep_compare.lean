-- Prove2me | solution 1 for GlobalTheory.HL.WitIndep.compare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:01.400804+00:00
-- url     : https://prove2.me/submissions/9c7e2a87-1beb-4306-9f73-c814d1cf4ff2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Theorems.Thm_GlobalTheory_HL_WitIndep_th_mul
import Theorems.Thm_GlobalTheory_HL_WitIndep_coords_mem
import Theorems.Thm_GlobalTheory_HL_WitIndep_frame_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FramePsi_psi_unitary_character
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_matrix
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_sum_l
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.WitIndep
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.HL.WitIndep
theorem _root_.solution {d : S.Datum} {Λ : Submodule L.O S.V} {n n' m m' : S.GLV}
    (H : S.IsTermW d Λ n n') (K : S.IsTermW d Λ m m') :
    (fun b => m (S.f b), fun b => m' (S.f' b)) ∈ S.frameCls (fun b => n (S.f b)) (fun b => n' (S.f' b)) ∧
      S.psi m * (S.psi' m')⁻¹ = S.psi n * (S.psi' n')⁻¹ := by
  obtain ⟨hI, hI', hn, hn', e, e', ht, -⟩ := H
  obtain ⟨-, -, hm, hm', f, f', kt, -⟩ := K
  have hs := mul_mem (inv_mem hn) hm
  have hs' := mul_mem (inv_mem hn') hm'
  obtain ⟨A, ⟨h0, h1⟩, hA⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hs
  obtain ⟨A', ⟨h0', h1'⟩, hA'⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hs'
  have a1 : ∀ j, m (S.f j) = ∑ i, A i j • n (S.f i) := fun j => by
    have := congrArg n (hA j)
    rw [show n ((n⁻¹ * m) (S.f j)) = m (S.f j) from n.apply_symm_apply _] at this
    simpa using this
  have a1' : ∀ j, m' (S.f' j) = ∑ i, A' i j • n' (S.f' i) := fun j => by
    have := congrArg n' (hA' j)
    rw [show n' ((n'⁻¹ * m') (S.f' j)) = m' (S.f' j) from n'.apply_symm_apply _] at this
    simpa using this
  have c1 := coords_mem S S.f S.es (.inl ⟨rfl, rfl⟩) _ hI n
  have c1' := coords_mem S S.f' S.es' (.inr ⟨rfl, rfl⟩) _ hI' n'
  rw [← e] at c1
  rw [← e'] at c1'
  have iA : IsIntM L A := fun i j => (c1 fun i => A i j).1 (by
    rw [← a1, f]; exact frame_mem S S.f S.es (.inl ⟨rfl, rfl⟩) _ hI m j) i
  have iA' : IsIntM L A' := fun i j => (c1' fun i => A' i j).1 (by
    rw [← a1', f']; exact frame_mem S S.f' S.es' (.inr ⟨rfl, rfl⟩) _ hI' m' j) i
  have cg : ∀ i j, algebraMap F E S.th⁻¹ * (A' i j - A i j) ∈ L.O := by
    intro i j
    choose y hy hy' using ht
    obtain ⟨z, hz, hz'⟩ := kt j
    refine (c1 fun i => algebraMap F E S.th⁻¹ * (A' i j - A i j)).1 ?_ i
    have b1 : ∀ i, y i = algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i)) := fun i => by
      rw [hy', smul_smul, th_mul, one_smul]
    have b2 : z = algebraMap F E S.th⁻¹ • (m' (S.f' j) - m (S.f j)) := by
      rw [hz', smul_smul, th_mul, one_smul]
    have : ∑ i, (algebraMap F E S.th⁻¹ * (A' i j - A i j)) • n (S.f i) = z - ∑ i, A' i j • y i := by
      rw [b2, a1, a1', ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [b1]
      module
    rw [this]
    exact Λ.sub_mem hz (Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, iA' i j⟩ : L.O) (hy i))
  refine ⟨⟨A, A', iA, iA', fun i j h => ⟨h0 i j h, h0' i j h⟩, fun i => ⟨h1 i, h1' i⟩,
    fun i j => ⟨_, cg i j, ?_⟩, a1, a1'⟩, ?_⟩
  · rw [← mul_assoc, mul_comm (algebraMap F E S.th), th_mul, one_mul]
  · obtain ⟨p1, p2, p3, -⟩ := FramePsi.psi_unitary_character L r k S
    have q1 := p1 n hn _ hs
    have q2 := p2 n' hn' _ hs'
    rw [mul_inv_cancel_left] at q1 q2
    have k1 : ∀ j, S.coef S.f S.es (n⁻¹ * m) j = A j.castSucc j.succ := fun j => by
      simp only [Frames.coef, Frames.h, hA, StdLat.hf_sum_l, hf_smul_l, S.dual]
      simp
    have k2 : ∀ j, S.coef S.f' S.es' (n'⁻¹ * m') j = A' j.castSucc j.succ := fun j => by
      simp only [Frames.coef, Frames.h, hA', StdLat.hf_sum_l, hf_smul_l, S.dual']
      simp
    have q3 : S.psi' (n'⁻¹ * m') = S.psi (n⁻¹ * m) := by
      have hO : ∑ j : Fin r, algebraMap F E S.th⁻¹ * (A' j.castSucc j.succ - A j.castSucc j.succ) ∈ L.O :=
        L.O.sum_mem fun j _ => cg _ _
      have h2 := (L.additive_character_dual_ring _).2 hO 1 L.O.one_mem
      simp only [Frames.psi, Frames.psi', Frames.psiOf, k1, k2]
      rw [← mul_one (L.psi0 (_ * ∑ j : Fin r, A _ _)), ← h2, ← AddChar.map_add_eq_mul, mul_one,
        ← Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      ring
    have q4 : S.psi (n⁻¹ * m) ≠ 0 := fun h => by simpa [h] using (p3 (n⁻¹ * m)).1
    rw [q1, q2, q3, mul_inv]
    field_simp
end GlobalTheory.HL.WitIndep
