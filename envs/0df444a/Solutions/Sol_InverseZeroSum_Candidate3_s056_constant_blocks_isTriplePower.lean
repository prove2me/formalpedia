-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s056_constant_blocks_isTriplePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:06.465403+00:00
-- url     : https://prove2.me/submissions/572be492-91cd-40ee-b385-0ad0fa5ca5d3

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s056_eight_constant_block_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    {S : PosSeq 24} (c : S039PackingCertificate S)
    (hs : c.s = 8) (hConst : S8RepresentativeSwapOutput S c)
    (rep : Fin c.s → Fin 24)
    (hRep : ∀ j, rep j ∈ c.blocks j) :
    IsTriplePower S (fun i : Fin 8 => S (rep (Fin.cast hs.symm i))) := by
  classical
  let idx : Fin 8 → Fin c.s := Fin.cast hs.symm
  have hIdxInj : Function.Injective idx := by
    intro i j hij
    have hh := congrArg (Fin.cast hs) hij
    simpa [idx] using hh
  let A : Fin 8 → Finset (Fin 24) := fun j => c.blocks (idx j)
  have hAcard : ∀ j, (A j).card = 3 := by
    intro j
    exact s056_eight_constant_block_card c hs hConst (idx j)
  let ord : (j : Fin 8) → Fin 3 ↪o Fin 24 :=
    fun j => (A j).orderEmbOfCardLe (by rw [hAcard j])
  have hOrdMem (j : Fin 8) (k : Fin 3) : ord j k ∈ A j := by
    simpa [ord] using Finset.orderEmbOfCardLe_mem
      (A j) (by rw [hAcard j]) k
  let q (i : Fin 24) : Fin 3 :=
    ⟨i.val / 8, by have hh := i.isLt; omega⟩
  let f (i : Fin 24) : Fin 24 := ord (baseIndex i) (q i)
  have hMem (i : Fin 24) : f i ∈ A (baseIndex i) := hOrdMem _ _
  have hFInj : Function.Injective f := by
    intro i j heq
    have hBase : baseIndex i = baseIndex j := by
      by_contra hNe
      have hBNe : idx (baseIndex i) ≠ idx (baseIndex j) := by
        intro hh
        exact hNe (hIdxInj hh)
      have hDisj := c.pairwise_disjoint _ _ hBNe
      have hMemJ : f i ∈ A (baseIndex j) := by
        rw [heq]
        exact hMem j
      exact (Finset.disjoint_left.mp hDisj) (hMem i) hMemJ
    have hQ : q i = q j := by
      have hh : ord (baseIndex i) (q i) =
          ord (baseIndex i) (q j) := by
        simpa [f, hBase] using heq
      exact (ord (baseIndex i)).injective hh
    have hMod : i.val % 8 = j.val % 8 := by
      simpa [baseIndex] using congrArg Fin.val hBase
    have hDiv : i.val / 8 = j.val / 8 := by
      simpa [q] using congrArg Fin.val hQ
    apply Fin.ext
    omega
  have hSurj : Function.Surjective f :=
    Finite.surjective_of_injective hFInj
  refine ⟨Equiv.ofBijective f ⟨hFInj, hSurj⟩, ?_⟩
  intro i
  change S (f i) = S (rep (idx (baseIndex i)))
  exact hConst.2.2 (idx (baseIndex i))
    (f i) (hMem i) (rep (idx (baseIndex i))) (hRep _)
end InverseZeroSum.Candidate3
