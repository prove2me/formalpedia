-- Prove2me | solution 1 for OAI.DimensionTen.exists_channel_fin21
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:59:49.626265+00:00
-- url     : https://prove2.me/submissions/96bf3d83-de96-45ea-b8d3-338024c64fbe

import Mathlib
import Definitions.Def_DimensionTenChannel
import Definitions.Def_OAIQ057D013
import Theorems.Thm_OAI_DimensionTen_main_channel_conditional_s2

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_ChannelModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace ChannelCompletion
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype n] [Fintype m] [Fintype p] in
lemma cp_comp {F : Map n m} {G : Map m p} (hG : CP G) (hF : CP F) : CP (G.comp F) := by
  intro k _ X hX
  exact hG k (amplify F X) (hF k X hX)

omit [Fintype n] [Fintype m] in
lemma amplify_omega [DecidableEq n] (F : Map n m) :
    amplify F (Matrix.vecMulVec (omega (n := n)) (star omega)) = choi F := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change F _ a b = F _ a b
  apply congrArg (fun X : Mat n => F X a b)
  ext x y
  simp only [Matrix.vecMulVec_apply, omega, Pi.star_apply, Matrix.single_apply]
  by_cases hix : i = x <;> by_cases hjy : j = y <;> simp [hix, hjy]

omit [Fintype m] in
lemma eb_choi [DecidableEq n] {F : Map n m} (hF : EntanglementBreaking F) :
    Separable (choi F) := by
  rw [← amplify_omega]
  exact hF.2 n _ (Matrix.posSemidef_vecMulVec_self_star _)

end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_ChannelCompletion
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace ChannelCompletion
variable {n m p q : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]

omit [Fintype n] [Fintype m] [Fintype p] [Fintype q] in
lemma separable_submatrix {Z : Mat (n × m)} (hZ : Separable Z) (e : p → n) (f : q → m) :
    Separable (Z.submatrix (Prod.map e f) (Prod.map e f)) := by
  obtain ⟨r, A, B, hA, hB, rfl⟩ := hZ
  refine ⟨r, (fun i => (A i).submatrix e e), (fun i => (B i).submatrix f f),
    (fun i => (hA i).submatrix e), (fun i => (hB i).submatrix f), ?_⟩
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [Matrix.submatrix_apply, Matrix.sum_apply]

end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_OrderedChannel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {n p : Type} [Fintype n] [Fintype p]

omit [Fintype n] [Fintype p] in
lemma rename_cp (e : p ≃ n) {F : Map n n} (hF : CP F) : CP (rename e F) := by
  intro k _ X hX
  exact (hF k (X.submatrix (Prod.map id e.symm) (Prod.map id e.symm))
    (hX.submatrix _)).submatrix (Prod.map id e)
omit [Fintype n] [Fintype p] in
lemma rename_transpose (e : p ≃ n) (F : Map n n) :
    rename e (transposeMap.comp F)=transposeMap.comp (rename e F) := by
  ext A i j
  rfl
omit [Fintype n] [Fintype p] in
lemma rename_ppt (e : p ≃ n) {F : Map n n} (hF : PPT F) : PPT (rename e F) := by
  refine ⟨rename_cp e hF.1,?_⟩
  rw [← rename_transpose]
  exact rename_cp e hF.2
lemma trace_submatrix_equivalence (e : p ≃ n) (A : Mat n) :
    Matrix.trace (A.submatrix e e)=Matrix.trace A := by
  exact e.sum_comp (fun i => A i i)
lemma rename_tracePreserving (e : p ≃ n) {F : Map n n} (hF : TracePreserving F) :
    TracePreserving (rename e F) := by
  intro A
  change Matrix.trace ((F (A.submatrix e.symm e.symm)).submatrix e e)=_
  rw [trace_submatrix_equivalence,hF,trace_submatrix_equivalence]
omit [Fintype n] [Fintype p] in
lemma rename_comp (e : p ≃ n) (G F : Map n n) :
    (rename e G).comp (rename e F)=rename e (G.comp F) := by
  ext A i j
  change G (((F (A.submatrix e.symm e.symm)).submatrix e e).submatrix e.symm e.symm) (e i) (e j)=_
  have h (B : Mat n) : (B.submatrix e e).submatrix e.symm e.symm=B := by
    ext a b
    simp only [Matrix.submatrix_apply,e.apply_symm_apply]
  rw [h]
  rfl
omit [Fintype n] [Fintype p] in
lemma eb_of_rename (e : p ≃ n) {F : Map n n} (hF : CP F)
    (h : EntanglementBreaking (rename e F)) : EntanglementBreaking F := by
  refine ⟨hF,?_⟩
  intro k _ X hX
  have hp := h.2 k (X.submatrix (Prod.map id e) (Prod.map id e)) (hX.submatrix _)
  have hs := separable_submatrix hp id e.symm
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  change F (fun a b => X (i.1,a) (j.1,b)) i.2 j.2=
    F (fun a b => X (i.1,e (e.symm a)) (j.1,e (e.symm b))) (e (e.symm i.2)) (e (e.symm j.2))
  simp only [e.apply_symm_apply]
end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Channel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving PPT channel with an entangled square, from the dimension-ten pair. -/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

theorem main_channel_fin21_conditional (hsr : PublishedChoi21) :
    ChannelCompletion.PPT channel21 ∧ ChannelCompletion.TracePreserving channel21 ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel21.comp channel21) := by
  obtain ⟨hP, hT, hE⟩ := main_channel_conditional_s2 hsr
  refine ⟨ChannelCompletion.rename_ppt _ hP,
    ChannelCompletion.rename_tracePreserving _ hT, ?_⟩
  intro hEB
  unfold channel21 at hEB
  rw [ChannelCompletion.rename_comp] at hEB
  exact hE (ChannelCompletion.eb_of_rename _ (ChannelCompletion.cp_comp hP.1 hP.1) hEB)

end DimensionTen

noncomputable section

namespace DimensionTen

theorem publishedChoi21 : PublishedChoi21 := by
  intro hEB
  exact ChannelCompletion.eb_choi hEB

theorem main_channel_fin21 :
    ChannelCompletion.PPT channel21 ∧ ChannelCompletion.TracePreserving channel21 ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel21.comp channel21) :=
  main_channel_fin21_conditional publishedChoi21

theorem exists_channel_fin21_oai :
    ∃ Θ : ChannelCompletion.Map (Fin 21) (Fin 21),
      ChannelCompletion.PPT Θ ∧ ChannelCompletion.TracePreserving Θ ∧
        ¬ ChannelCompletion.EntanglementBreaking (Θ.comp Θ) :=
  ⟨channel21, main_channel_fin21⟩

end DimensionTen

end
end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.exists_channel_fin21_oai := @OAI.DimensionTen.exists_channel_fin21_oai
