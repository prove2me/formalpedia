-- Prove2me | solution 1 for OAI.DFVSGames.Inverse.ShortcodeFromGrassmann.inversePrinciple_of_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:01:42.776069+00:00
-- url     : https://prove2.me/submissions/07f5454d-8dcf-46cc-865f-2420598beb9a

import Mathlib
import Definitions.Def_OAIQ085D027

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSlices
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

theorem Slice.constantAgreement_eq_affine {ell m : ℕ} (S : Slice ell m)
    (f : Mat ell m → Vector ell) (u : Vector ell) :
    S.constantAgreement f u = S.affineAgreement f 0 u := by
  simp [Slice.constantAgreement, Slice.affineAgreement]

theorem hasAffineSlice_of_constant {ell m : ℕ} (f : Mat ell m → Vector ell)
    (α : ℝ) (r : ℕ) (S : Slice ell m) (hrows : S.rows ≤ r)
    (hcolumns : S.columns ≤ r) (hne : S.points.Nonempty) (u : Vector ell)
    (h : α ≤ S.constantAgreement f u) : HasAffineSlice f α r := by
  exact ⟨S, hrows, hcolumns, hne, 0, u, by
    simpa only [S.constantAgreement_eq_affine f u] using h⟩

end
end DFVSGames.Inverse.Shortcode

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_KMSMomentConstants
attribute [-instance] _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

theorem inter_chart_eq (S I C : Finset Ω) (hSC : S ⊆ C) :
    S ∩ (I ∩ C) = S ∩ I := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hS, hI, _⟩
    exact ⟨hS, hI⟩
  · rintro ⟨hS, hI⟩
    exact ⟨hS, hI, hSC hS⟩

theorem chart_inter_nonempty (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) : (I ∩ C).Nonempty := by
  obtain ⟨x, hx⟩ := hSI
  exact ⟨x, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).2, hSC (Finset.mem_inter.mp hx).1⟩⟩

theorem relativeDensity_le_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hIC : (I ∩ C).Nonempty) :
    relativeDensity S I ≤ relativeDensity S (I ∩ C) := by
  unfold relativeDensity
  rw [inter_chart_eq S I C hSC]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hIC)
  · exact Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)

theorem density_bound_passes_to_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) {α : ℝ} (hα : α ≤ relativeDensity S I) :
    (I ∩ C).Nonempty ∧ α ≤ relativeDensity S (I ∩ C) := by
  have hIC := chart_inter_nonempty S I C hSC hSI
  exact ⟨hIC, hα.trans (relativeDensity_le_chart S I C hSC hIC)⟩

end FiniteDensity

end
end DFVSGames.Inverse.KMS

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_KMSMomentScalar
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem card_lines_binary [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E] :
    Nat.card (Lines (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  classical
  let spanMap : {v : E // v ≠ 0} → Lines (ZMod 2) E := fun v =>
    ⟨Submodule.span (ZMod 2) {v.val}, finrank_span_singleton v.property⟩
  have hinj : Function.Injective spanMap := by
    intro v w h
    have hv : v.val ∈ Submodule.span (ZMod 2) {w.val} := by
      have hs : Submodule.span (ZMod 2) {v.val} =
          Submodule.span (ZMod 2) {w.val} := congrArg Subtype.val h
      rw [← hs]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hcases c with hc0 | hc1
    · exact False.elim (v.property (by simpa [hc0] using hc.symm))
    · exact Subtype.ext (by simpa [hc1] using hc.symm)
  have hsurj : Function.Surjective spanMap := by
    intro L
    obtain ⟨v, hv0, _⟩ := (finrank_eq_one_iff').mp L.property
    have hv : (v : E) ≠ 0 := fun h => hv0 (Subtype.ext h)
    refine ⟨⟨v.val, hv⟩, Subtype.ext ?_⟩
    exact (eq_span_singleton_of_mem_of_finrank_eq_one L.property v.property hv).symm
  let e : {v : E // v ≠ 0} ≃ Lines (ZMod 2) E := Equiv.ofBijective spanMap ⟨hinj, hsurj⟩
  let coords : E ≃ₗ[ZMod 2] (Fin (finrank (ZMod 2) E) → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  let : Finite E := Finite.of_equiv _ coords.symm.toEquiv
  let : Fintype E := Fintype.ofFinite E
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp

theorem card_hyperplanes_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] :
    Nat.card (Hyperplanes (ZMod 2) E) = 2 ^ finrank (ZMod 2) E - 1 := by
  rw [Nat.card_congr (hyperplanesEquivDualLines (K := ZMod 2) (E := E)),
    card_lines_binary, Subspace.dual_finrank_eq]

theorem card_extensions_binary [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (H : Submodule (ZMod 2) E) :
    Nat.card (Extensions H) = 2 ^ finrank (ZMod 2) (E ⧸ H) - 1 := by
  rw [Nat.card_congr (extensionsEquivLines H), card_lines_binary]

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_MatrixChartDegreeNeighbors
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem card_other_extensions_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E)
    (H : HyperplanesBelow L) :
    Nat.card {W : Extensions H.val // W.val ≠ L} =
      2 ^ finrank (ZMod 2) (E ⧸ H.val) - 2 := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let base : Extensions H.val := ⟨L, H.property.1, H.property.2.symm⟩
  let : Fintype (Extensions H.val) := Fintype.ofFinite _
  have heq : (fun W : Extensions H.val => W.val ≠ L) = (fun W => W ≠ base) := by
    funext W
    apply propext
    apply not_congr
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg Subtype.val h
  rw [heq]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
    card_extensions_binary]
  omega

theorem card_grassmann_neighbors_binary [Module (ZMod 2) E] [Finite E]
    [FiniteDimensional (ZMod 2) E] (L : Submodule (ZMod 2) E) (m : ℕ)
    (hE : finrank (ZMod 2) E = finrank (ZMod 2) L + m) :
    Nat.card (GrassmannNeighbors L) =
      (2 ^ finrank (ZMod 2) L - 1) * (2 ^ (m + 1) - 2) := by
  classical
  let : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun H : Submodule (ZMod 2) E => (H : Set E))
      SetLike.coe_injective
  let : Fintype (HyperplanesBelow L) := Fintype.ofFinite _
  rw [Nat.card_congr (neighborsEquivExtensionData L), Nat.card_sigma]
  have hterm (H : HyperplanesBelow L) :
      Nat.card {W : Extensions H.val // W.val ≠ L} = 2 ^ (m + 1) - 2 := by
    rw [card_other_extensions_binary]
    have h := H.val.finrank_quotient_add_finrank
    have hH := H.property.2
    congr 2
    omega
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card,
    Nat.card_congr (hyperplanesBelowEquiv L), card_hyperplanes_binary]

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem lowerRows_le_graph_iff {ι : Type*} (d : ι → X) (s : ι → Y)
    (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ↔ ∀ i, T (d i) = s i := by
  rw [lowerRows, Submodule.span_le]
  constructor
  · intro h i
    exact (h ⟨i, rfl⟩).symm
  · rintro h _ ⟨i, rfl⟩
    exact (h i).symm

theorem graph_le_upperColumns_iff {ι : Type*}
    (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    T.graph ≤ upperColumns t q ↔ ∀ i, (q i).comp T = t i := by
  constructor
  · intro h i
    apply LinearMap.ext
    intro x
    have hx := h (show (x, T x) ∈ T.graph from rfl)
    have hi := ((Submodule.mem_iInf _).mp hx) i
    exact sub_eq_zero.mp hi
  · intro h x hx
    apply (Submodule.mem_iInf _).mpr
    intro i
    change q i x.2 - t i x.1 = 0
    rw [hx]
    exact sub_eq_zero.mpr (congrArg (fun f : X →ₗ[K] K => f x.1) (h i))

theorem interval_iff_slice {ι κ : Type*} (d : ι → X) (s : ι → Y)
    (t : κ → X →ₗ[K] K) (q : κ → Y →ₗ[K] K) (T : X →ₗ[K] Y) :
    lowerRows d s ≤ T.graph ∧ T.graph ≤ upperColumns t q ↔
      (∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j) := by
  rw [lowerRows_le_graph_iff, graph_le_upperColumns_iff]

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonFibers
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

theorem card_grassmann_neighbors_graph (T : CoordinateMatrix ell m) :
    Nat.card (GrassmannNeighbors T.graph) =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  have h := card_grassmann_neighbors_binary T.graph m (by
    rw [finrank_graph, Module.finrank_prod]
    simp)
  simpa only [finrank_graph, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] using h

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_comp_vecMulLinear (M : Matrix ι κ K) (q : κ → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional (M *ᵥ q) := by
  apply LinearMap.ext
  intro x
  change q ⬝ᵥ (x ᵥ* M) = (M *ᵥ q) ⬝ᵥ x
  rw [← Matrix.mulVec_transpose, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem column_equation_iff (M : Matrix ι κ K) (q : κ → K) (t : ι → K) :
    (dotFunctional q).comp M.vecMulLinear = dotFunctional t ↔ M *ᵥ q = t := by
  rw [dotFunctional_comp_vecMulLinear]
  exact dotFunctional_injective.eq_iff

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Module

theorem card_full_neighbors {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
  classical
  have h : Nat.card {W : KMS.Vertex (ell + m) ell //
      KMS.Adjacent (matrixVertex M) W} =
      (2 ^ ell - 1) * (2 ^ (m + 1) - 2) := by
    rw [← Nat.card_congr (kmsNeighborsEquiv (matrixVertex M))]
    change Nat.card (GrassmannNeighbors
      ((matrixGraph M).map (coordinateJoin (ZMod 2) ell m).toLinearMap)) = _
    rw [← Nat.card_congr (grassmannNeighborsMapEquiv
      (coordinateJoin (ZMod 2) ell m) (matrixGraph M))]
    exact card_grassmann_neighbors_graph M.vecMulLinear
  simpa only [Nat.card_eq_fintype_card, KMS.neighbors, Fintype.card_subtype] using h

theorem card_full_neighbors_twice {ell m : Nat} (M : Matrix (Fin ell) (Fin m) (ZMod 2)) :
    (KMS.neighbors (matrixVertex M)).card =
      2 * ((2 ^ ell - 1) * (2 ^ m - 1)) := by
  rw [card_full_neighbors]
  have hpow : 2 ^ (m + 1) - 2 = 2 * (2 ^ m - 1) := by
    rw [pow_succ, Nat.mul_sub_left_distrib]
    simp [Nat.mul_comm]
  rw [hpow]
  ac_rfl

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KMSBasisComparisonRetention
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem span_basis_values {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    Submodule.span K (Set.range fun i => (b i).val) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp', Submodule.coe_subtype] using h

theorem lowerRows_basis {ι : Type*} (A : Submodule K (X × Y))
    (b : Module.Basis ι K A) :
    lowerRows (fun i => (b i).val.1) (fun i => (b i).val.2) = A := by
  exact span_basis_values A b

theorem mem_iff_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) (x : X × Y) :
    x ∈ B ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator (b i).val).mp (b i).property x hx
  · intro h
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff B x).mp
    intro φ hφ
    let ev : B.dualAnnihilator →ₗ[K] K :=
      (Module.Dual.eval K (X × Y) x).comp B.dualAnnihilator.subtype
    have hev : ev = 0 := b.ext (fun i => h i)
    exact congrArg (fun f : B.dualAnnihilator →ₗ[K] K => f ⟨φ, hφ⟩) hev

theorem functional_coordinate_decomposition (φ : (X × Y) →ₗ[K] K) (x : X) (y : Y) :
    φ (x, y) = φ (x, 0) + φ (0, y) := by
  have h : (x, y) = (x, 0) + (0, y) := by simp
  rw [h, map_add]

theorem upperColumns_annihilator_basis {ι : Type*} (B : Submodule K (X × Y))
    (b : Module.Basis ι K B.dualAnnihilator) :
    upperColumns
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) = B := by
  ext x
  rw [mem_iff_annihilator_basis B b]
  simp only [upperColumns, Submodule.mem_iInf]
  change (∀ i, x ∈ LinearMap.ker
    (((b i).val.comp (LinearMap.inr K X Y)).comp (LinearMap.snd K X Y) -
      (-((b i).val.comp (LinearMap.inl K X Y))).comp (LinearMap.fst K X Y))) ↔ _
  constructor <;> intro h i
  · have hi := h i
    change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0 at hi
    rw [functional_coordinate_decomposition]
    simpa only [sub_neg_eq_add, add_comm] using hi
  · change (b i).val (0, x.2) - -(b i).val (x.1, 0) = 0
    have hi := h i
    rw [functional_coordinate_decomposition] at hi
    simpa only [sub_neg_eq_add, add_comm] using hi

theorem exists_interval_coordinates [FiniteDimensional K X] [FiniteDimensional K Y]
    (A B : Submodule K (X × Y)) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → X) (s : Fin n_r → Y)
      (t : Fin n_c → X →ₗ[K] K) (q : Fin n_c → Y →ₗ[K] K),
      n_r = Module.finrank K A ∧ n_c = Module.finrank K ((X × Y) ⧸ B) ∧
      ∀ T : X →ₗ[K] Y,
        (A ≤ T.graph ∧ T.graph ≤ B) ↔
          ((∀ i, T (d i) = s i) ∧ (∀ j, (q j).comp T = t j)) := by
  let a := Module.finBasis K A
  let : Module.Free K B.dualAnnihilator := Module.Free.of_divisionRing K B.dualAnnihilator
  let b := Module.finBasis K B.dualAnnihilator
  refine ⟨Module.finrank K A, Module.finrank K B.dualAnnihilator,
    (fun i => (a i).val.1), (fun i => (a i).val.2),
    (fun i => -((b i).val.comp (LinearMap.inl K X Y))),
    (fun i => (b i).val.comp (LinearMap.inr K X Y)), rfl, ?_, ?_⟩
  · exact (Subspace.quotEquivAnnihilator B).finrank_eq.symm
  · intro T
    have h := interval_iff_slice (fun i => (a i).val.1) (fun i => (a i).val.2)
      (fun i => -((b i).val.comp (LinearMap.inl K X Y)))
      (fun i => (b i).val.comp (LinearMap.inr K X Y)) T
    simpa only [lowerRows_basis A a, upperColumns_annihilator_basis B b] using h

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem exists_matrix_interval_slice (A B : Submodule K ((ι → K) × (κ → K))) :
    ∃ (n_r n_c : Nat) (d : Fin n_r → ι → K) (s : Fin n_r → κ → K)
      (t : Fin n_c → ι → K) (q : Fin n_c → κ → K),
      n_r = Module.finrank K A ∧
      n_c = Module.finrank K (((ι → K) × (κ → K)) ⧸ B) ∧
      ∀ M : Matrix ι κ K,
        (A ≤ matrixGraph M ∧ matrixGraph M ≤ B) ↔
          ((∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j)) := by
  classical
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_interval_coordinates A B
  choose tv htv using (fun j => dotFunctional_surjective (t j))
  choose qv hqv using (fun j => dotFunctional_surjective (q j))
  refine ⟨nr, nc, d, s, tv, qv, hnr, hnc, ?_⟩
  intro M
  rw [h M.vecMulLinear]
  have hj (j : Fin nc) : (q j).comp M.vecMulLinear = t j ↔ M *ᵥ qv j = tv j := by
    rw [← hqv j, ← htv j]
    exact column_equation_iff M (qv j) (tv j)
  simp only [Matrix.vecMulLinear_apply, hj]

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.MatrixChart

open Matrix

theorem exists_shortcode_slice {ell m : Nat}
    (A B : Submodule (ZMod 2) (KMS.Ambient (ell + m))) :
    ∃ S : Shortcode.Slice ell m,
      S.rows = Module.finrank (ZMod 2) A ∧
      S.columns = (ell + m) - Module.finrank (ZMod 2) B ∧
      ∀ M : Shortcode.Mat ell m,
        S.Contains M ↔ A ≤ (matrixVertex M).val ∧ (matrixVertex M).val ≤ B := by
  classical
  let e := coordinateJoin (ZMod 2) ell m
  let A' := A.comap e.toLinearMap
  let B' := B.comap e.toLinearMap
  have hA : Module.finrank (ZMod 2) A' = Module.finrank (ZMod 2) A := by
    rw [show A' = A.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e A]
    exact e.symm.finrank_map_eq A
  have hB : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B := by
    rw [show B' = B.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e B]
    exact e.symm.finrank_map_eq B
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A' B'
  have hE : Module.finrank (ZMod 2)
      ((Fin ell → ZMod 2) × (Fin m → ZMod 2)) = ell + m := by simp
  have hnc' : nc = (ell + m) - Module.finrank (ZMod 2) B := by
    simpa only [Submodule.finrank_quotient, hE, hB] using hnc
  let S : Shortcode.Slice ell m := ⟨nr, nc, d, s, q, t⟩
  refine ⟨S, hnr.trans hA, hnc', ?_⟩
  intro M
  have hcontains : S.Contains M ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨fun i => funext (hr i), hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨fun i j => congrFun (hr i) j, hc⟩
  rw [hcontains, ← h M]
  have hlow : A' ≤ matrixGraph M ↔ A ≤ (matrixVertex M).val := by
    change A.comap e.toLinearMap ≤ matrixGraph M ↔
      A ≤ (matrixGraph M).map e.toLinearMap
    have hh := Submodule.comap_le_comap_iff_of_surjective
      (f := e.toLinearMap) e.surjective (p := A)
      (q := (matrixGraph M).map e.toLinearMap)
    simpa only [Submodule.comap_map_eq_of_injective e.injective] using hh
  have hupp : matrixGraph M ≤ B' ↔ (matrixVertex M).val ≤ B :=
    Submodule.map_le_iff_le_comap.symm
  exact and_congr hlow hupp

end DFVSGames.Inverse.MatrixChart

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

theorem exists_zeroFactorMass_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ ell m : ℕ, N ≤ ell → N ≤ m → zeroFactorMass ell m ≤ η / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro ell m hell hm
  have hpow (n : ℕ) (hn : N ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ η / 4 := by
    have hmon : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    simpa only [one_div, inv_pow] using hmon.trans hN.le
  have hell' := hpow ell hell
  have hm' := hpow m hm
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (ell + m))⁻¹ := by positivity
  unfold zeroFactorMass
  linarith

theorem inversePrinciple_of_expansion_and_chart
    (hKMS : KMS.ExpansionPrinciple) (hChart : ChartFiberRetention) :
    InversePrinciple := by
  intro η hη hη1
  obtain ⟨α, hαpos, hαone, r, hr, ellKMS, hKMSell⟩ :=
    hKMS (η / 4) (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_zeroFactorMass_threshold hη
  refine ⟨α, hαpos, hαone, r, hr, max ellKMS (max 1 N), ?_⟩
  intro ell hell
  have hellKMS : ellKMS ≤ ell := (le_max_left _ _).trans hell
  have hellone : 1 ≤ ell := (le_max_left 1 N).trans ((le_max_right _ _).trans hell)
  have hellN : N ≤ ell := (le_max_right 1 N).trans ((le_max_right _ _).trans hell)
  obtain ⟨nKMS, hKMSn⟩ := hKMSell ell hellKMS
  refine ⟨max nKMS (max 1 N), ?_⟩
  intro m hm f haccept
  have hmKMS : nKMS ≤ m := (le_max_left _ _).trans hm
  have hmone : 1 ≤ m := (le_max_left 1 N).trans ((le_max_right _ _).trans hm)
  have hmN : N ≤ m := (le_max_right 1 N).trans ((le_max_right _ _).trans hm)
  obtain ⟨y, hnonempty, hretention⟩ :=
    hChart hellone hmone η hη hη1 (hN ell m hellN hmN) f haccept
  obtain ⟨A, B, _hAB, hbudget, hintersection, hdense⟩ :=
    hKMSn (ell + m) (by omega) (liftedFiber f y) hnonempty hretention
  change Module.finrank (ZMod 2) A +
    ((ell + m) - Module.finrank (ZMod 2) B) ≤ r at hbudget
  obtain ⟨S, hrows, hcolumns, hcontains⟩ := exists_shortcode_slice A B
  apply hasAffineSlice_of_dense_interval f y (KMS.interval A B) S
  · intro M
    simpa only [KMS.interval, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcontains M
  · omega
  · omega
  · exact hintersection
  · exact hdense

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

theorem card_matrixVertexChartNeighbors (M : Mat ell m) :
    Nat.card (MatrixVertexChartNeighbors M) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  rw [← Nat.card_congr (vectorFactorsEquivMatrixVertexChartNeighbors M)]
  simp only [NonzeroVectorFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Shortcode.Vector, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end DFVSGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_EqualityFiber
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

theorem relativeDensity_filter_eq_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (P : Ω → Prop) [DecidablePred P] :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

theorem retention_image {X : Type*} [DecidableEq X] {n ell : ℕ}
    (S : Finset X) (e : X → KMS.Vertex n ell) (he : Function.Injective e) :
    KMS.retention (S.image e) =
      S.expect fun x => KMS.relativeDensity (S.image e) (KMS.neighbors (e x)) := by
  have h : KMS.retention (S.image e) =
      (S.image e).expect fun L => KMS.relativeDensity (S.image e) (KMS.neighbors L) := by
    rw [Finset.expect_eq_sum_div_card]
    rfl
  rw [h]
  exact Finset.expect_image he.injOn

theorem relativeDensity_neighbors_eq_nonzero_average_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M)) =
      (𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  let C := KMS.neighbors (matrixVertex M) ∩ matrixChart ell m
  have hC : C = Finset.univ.filter (fun L : KMS.Vertex (ell + m) ell =>
      KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m) := by
    ext L
    simp [C, KMS.neighbors]
  have hcardC : C.card = (2 ^ ell - 1) * (2 ^ m - 1) := by
    rw [hC]
    have h := card_matrixVertexChartNeighbors M
    simpa only [MatrixVertexChartNeighbors, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using h
  have hcard : (KMS.neighbors (matrixVertex M)).card = 2 * C.card := by
    rw [hcardC]
    exact card_full_neighbors_twice M
  have hnumerator : liftedFiber f y ∩ C =
      liftedFiber f y ∩ KMS.neighbors (matrixVertex M) :=
    KMS.inter_chart_eq _ _ _ (liftedFiber_subset_chart f y)
  have hhalf : KMS.relativeDensity (liftedFiber f y)
      (KMS.neighbors (matrixVertex M)) =
        KMS.relativeDensity (liftedFiber f y) C / 2 := by
    unfold KMS.relativeDensity
    rw [hcard, ← hnumerator, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm (2 : ℝ), div_mul_eq_div_div]
  rw [hhalf]
  congr 1
  rw [hC]
  trans (𝔼 L : MatrixVertexChartNeighbors M,
    if L.val ∈ liftedFiber f y then (1 : ℝ) else 0)
  · exact relativeDensity_filter_eq_expect (liftedFiber f y)
      (fun L => KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m)
  symm
  apply Fintype.expect_equiv (vectorFactorsEquivMatrixVertexChartNeighbors M)
  intro p
  simp only [vectorFactorsEquivMatrixVertexChartNeighbors_apply,
    matrixVertex_mem_liftedFiber]

theorem liftedFiber_retention_eq_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    KMS.retention (liftedFiber f y) =
      (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  unfold liftedFiber
  rw [retention_image _ _ matrixVertex_injective]
  change (𝔼 M ∈ matrixFiber f y,
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M))) = _
  simp_rw [relativeDensity_neighbors_eq_nonzero_average_half]
  exact (Finset.expect_div _ _ _).symm

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical
open DFVSGames.Foundations.Information

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem sum_fiberMass (p : X → ℝ) (f : X → Y) :
    ∑ y, fiberMass p f y = ∑ x, p x := by
  classical
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
theorem fiberMass_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : X → Y) (y : Y) : 0 ≤ fiberMass p f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split
  · exact hp x
  · exact le_rfl

omit [Fintype Y] in
theorem fiberFlow_nonneg (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x x', 0 ≤ k x x')
    (f : X → Y) (y : Y) : 0 ≤ fiberFlow p k f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hp x)
  apply Finset.sum_nonneg
  intro x' _
  apply mul_nonneg (hk x x')
  split <;> norm_num

omit [Fintype Y] in
theorem fiberFlow_le_mass (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) (y : Y) : fiberFlow p k f y ≤ fiberMass p f y := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases h : f x = y
  · simp only [h, true_and, ite_true, if_true]
    have hinner : (∑ x', k x x' * if f x' = y then 1 else 0) ≤ 1 := by
      calc
        _ ≤ ∑ x', k x x' := by
          apply Finset.sum_le_sum
          intro x' _
          split <;> simp [(hk x).1 x']
        _ = 1 := (hk x).2
    simpa using mul_le_mul_of_nonneg_left hinner (hp x)
  · simp [h]

private theorem sum_sameFiber_indicator_inline_EqualityFiber (a b : Y) :
    (∑ y, if a = y ∧ b = y then (1 : ℝ) else 0) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    have h' : ¬ (a = y ∧ b = y) := fun hy => h (hy.1.trans hy.2.symm)
    simp [h']

theorem sum_fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) :
    ∑ y, fiberFlow p k f y = equalityAcceptance p k f := by
  classical
  unfold fiberFlow equalityAcceptance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x' _
  rw [← Finset.mul_sum, sum_sameFiber_indicator_inline_EqualityFiber]

theorem exists_positive_mass_le_flow (mass flow : Y → ℝ)
    (hmass : IsProbability mass) (_hflow : ∀ y, 0 ≤ flow y)
    (hzero : ∀ y, mass y = 0 → flow y = 0)
    {η : ℝ} (haccept : η ≤ ∑ y, flow y) :
    ∃ y, 0 < mass y ∧ η * mass y ≤ flow y := by
  classical
  by_contra hnone
  have hless (y : Y) (hy : 0 < mass y) : flow y < η * mass y := by
    apply lt_of_not_ge
    intro h
    exact hnone ⟨y, hy, h⟩
  have hle (y : Y) : flow y ≤ η * mass y := by
    rcases eq_or_lt_of_le (hmass.1 y) with hz | hz
    · simp [← hz, hzero y hz.symm]
    · exact (hless y hz).le
  have hex : ∃ y, 0 < mass y := by
    by_contra hn
    have hall (y : Y) : mass y = 0 := le_antisymm (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
      (hmass.1 y)
    have := hmass.2
    simp [hall] at this
  obtain ⟨y, hy⟩ := hex
  have hstrict : (∑ y, flow y) < ∑ y, η * mass y := by
    exact Finset.sum_lt_sum (fun y _ => hle y) ⟨y, Finset.mem_univ y, hless y hy⟩
  rw [← Finset.mul_sum, hmass.2, mul_one] at hstrict
  exact (not_lt_of_ge haccept) hstrict

theorem exists_fiber_retention (p : X → ℝ) (k : X → X → ℝ)
    (hp : IsProbability p) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) {η : ℝ} (haccept : η ≤ equalityAcceptance p k f) :
    ∃ y, 0 < fiberMass p f y ∧ η ≤ fiberFlow p k f y / fiberMass p f y := by
  have hmass : IsProbability (fiberMass p f) :=
    ⟨fiberMass_nonneg p hp.1 f, (sum_fiberMass p f).trans hp.2⟩
  have hflow := fiberFlow_nonneg p k hp.1 (fun x => (hk x).1) f
  have hzero (y : Y) (hy : fiberMass p f y = 0) : fiberFlow p k f y = 0 := by
    apply le_antisymm _ (hflow y)
    simpa [hy] using fiberFlow_le_mass p k hp.1 hk f y
  obtain ⟨y, hy, hret⟩ := exists_positive_mass_le_flow (fiberMass p f)
    (fiberFlow p k f) hmass hflow hzero (by simpa [sum_fiberFlow] using haccept)
  exact ⟨y, hy, (le_div_iff₀ hy).2 hret⟩

theorem nonzero_retention_ge_half {η p₀ R : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hp₀ : 0 ≤ p₀) (hp₀η : p₀ ≤ η / 2)
    (haccept : η ≤ p₀ + (1 - p₀) * R) : η / 2 ≤ R := by
  have hp₀1 : p₀ < 1 := by linarith
  have hden : 0 < 1 - p₀ := by linarith
  have hprod : η / 2 * (1 - p₀) ≤ (1 - p₀) * R := by nlinarith
  nlinarith

end
end DFVSGames.Inverse.EqualityFiber

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Foundations.Information

theorem matrixWeight_probability (ell m : ℕ) :
    IsProbability (matrixWeight (ell := ell) (m := m)) := by
  constructor
  · intro M
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [matrixWeight, hcard]

theorem matrixKernel_nonneg {ell m : ℕ} (M N : Mat ell m) :
    0 ≤ matrixKernel M N := by
  apply Finset.expect_nonneg
  intro a _
  apply Finset.expect_nonneg
  intro l _
  split <;> norm_num

theorem matrixKernel_probability {ell m : ℕ} (M : Mat ell m) :
    IsProbability (matrixKernel M) := by
  refine ⟨matrixKernel_nonneg M, ?_⟩
  unfold matrixKernel
  rw [← Finset.expect_sum_comm]
  have hpoint (a : Vector ell) :
      (∑ N : Mat ell m, 𝔼 l : Vector m,
        if N = M + rankOne a l then (1 : ℝ) else 0) = 1 := by
    rw [← Finset.expect_sum_comm]
    simp
  simp only [hpoint]
  simp

theorem matrixKernel_equality {ell m : ℕ} (f : Mat ell m → Vector ell)
    (M : Mat ell m) :
    (∑ N, matrixKernel M N * if f M = f N then (1 : ℝ) else 0) =
      𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0 := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem equalityAcceptance_eq_kernel {ell m : ℕ} (f : Mat ell m → Vector ell) :
    equalityAcceptance f = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
  calc
    equalityAcceptance f = ∑ M, matrixWeight M *
        (𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then (1 : ℝ) else 0) := by
      unfold equalityAcceptance matrixWeight
      rw [Fintype.expect_eq_sum_div_card]
      simp only [div_eq_mul_inv, ← Finset.mul_sum, mul_comm]
    _ = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
      unfold EqualityFiber.equalityAcceptance
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      convert (matrixKernel_equality f M).symm using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro N _
      by_cases h : f M = f N <;> simp [h]

theorem exists_output_fiber {ell m : ℕ} (f : Mat ell m → Vector ell)
    {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y : Vector ell, 0 < EqualityFiber.fiberMass matrixWeight f y ∧
      η ≤ EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
        EqualityFiber.fiberMass matrixWeight f y := by
  apply EqualityFiber.exists_fiber_retention matrixWeight matrixKernel
    (matrixWeight_probability ell m) matrixKernel_probability f
  rwa [← equalityAcceptance_eq_kernel]

end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode DFVSGames.Foundations.Information

theorem matrixKernel_average {ell m : ℕ} (M : Mat ell m) (g : Mat ell m → ℝ) :
    (∑ N, matrixKernel M N * g N) = 𝔼 a, 𝔼 l, g (M + rankOne a l) := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp [ite_mul]

theorem fiberMass_eq_card {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberMass matrixWeight f y =
      ((matrixFiber f y).card : ℝ) / Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberMass
  calc
    _ = ∑ M ∈ matrixFiber f y, matrixWeight M := by
      rw [matrixFiber, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro M _
      by_cases h : f M = y <;> simp [h]
    _ = _ := by simp [matrixWeight, div_eq_mul_inv]

theorem fiberMass_pos_iff {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    0 < EqualityFiber.fiberMass matrixWeight f y ↔ (matrixFiber f y).Nonempty := by
  rw [fiberMass_eq_card]
  have hcard : (0 : ℝ) < Fintype.card (Mat ell m) := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Finset.card_pos]

theorem fiberFlow_eq {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y =
      (∑ M ∈ matrixFiber f y,
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) /
        Fintype.card (Mat ell m) := by
  unfold EqualityFiber.fiberFlow
  simp_rw [matrixKernel_average]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [matrixFiber, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro M _
  by_cases h : f M = y
  · simp [h, matrixWeight, mul_comm]
  · simp [h]

theorem fiber_retention_eq_factor_average {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
      EqualityFiber.fiberMass matrixWeight f y =
        𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  rw [fiberFlow_eq, fiberMass_eq_card]
  have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hswap : (𝔼 a, 𝔼 l, fiberFactorRetention f y a l) =
      (matrixFiber f y).expect (fun M =>
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
    unfold fiberFactorRetention
    calc
      _ = 𝔼 a, (matrixFiber f y).expect (fun M =>
          𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
        apply Finset.expect_congr rfl
        intro a _
        rw [Finset.expect_comm]
      _ = _ := Finset.expect_comm _ _ _
  rw [hswap, Finset.expect_eq_sum_div_card]
  simp [div_div_div_cancel_right₀ hcard]

theorem fiberFactorRetention_zero_left {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (l : Vector m) :
    fiberFactorRetention f y 0 l = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne (0 : Vector ell) l) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem fiberFactorRetention_zero_right {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (a : Vector ell) :
    fiberFactorRetention f y a 0 = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne a (0 : Vector m)) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem exists_output_fiber_factor_retention {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧ η ≤ 𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  obtain ⟨y, hy, hret⟩ := Shortcode.exists_output_fiber f haccept
  exact ⟨y, (fiberMass_pos_iff f y).mp hy,
    by simpa only [fiber_retention_eq_factor_average] using hret⟩

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode

theorem uniform_pair_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Zero A] [Zero B] (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) *
        (𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0}, h p.1.val p.2.val) := by
  let R : ℝ := 𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0},
    h p.1.val p.2.val
  have : Nonempty A := ⟨0⟩
  have : Nonempty B := ⟨0⟩
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNA : (Fintype.card {a : A // a ≠ 0} : ℝ) =
      (Fintype.card A : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNB : (Fintype.card {b : B // b ≠ 0} : ℝ) =
      (Fintype.card B : ℝ) - 1 := by
    have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : B => (1 : ℝ)) 0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
    linarith
  have hNZ : (∑ a : {a : A // a ≠ 0}, ∑ b : {b : B // b ≠ 0}, h a.val b.val) =
      (Fintype.card {a : A // a ≠ 0} : ℝ) *
        (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    simpa only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type] using
      (Fintype.card_mul_expect
        (fun p : {a : A // a ≠ 0} × {b : B // b ≠ 0} => h p.1.val p.2.val)).symm
  have hinner (a : A) : (∑ b : B, h a b) =
      1 + ∑ b : {b : B // b ≠ 0}, h a b.val := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ 0, hright]
  have hsum : (∑ a : A, ∑ b : B, h a b) =
      (Fintype.card B : ℝ) + (Fintype.card {a : A // a ≠ 0} : ℝ) +
        (Fintype.card {a : A // a ≠ 0} : ℝ) *
          (Fintype.card {b : B // b ≠ 0} : ℝ) * R := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a : A => ∑ b : B, h a b) 0]
    simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, hNZ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hfull : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) = ∑ a, ∑ b, h a b := by
    calc
      _ = (Fintype.card B : ℝ) *
          ((Fintype.card A : ℝ) * (𝔼 a, 𝔼 b, h a b)) := by ring
      _ = (Fintype.card B : ℝ) * (∑ a, 𝔼 b, h a b) := by
        rw [Fintype.card_mul_expect]
      _ = _ := by
        rw [Finset.mul_sum]
        simp_rw [Fintype.card_mul_expect]
  have hbalance : (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
      (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ) + (Fintype.card B : ℝ) - 1 +
        ((Fintype.card A : ℝ) - 1) * ((Fintype.card B : ℝ) - 1) * R := by
    rw [hfull, hsum, hNA, hNB]
    ring
  apply mul_left_cancel₀ (mul_ne_zero hA hB)
  rw [hbalance]
  change _ = (Fintype.card A : ℝ) * (Fintype.card B : ℝ) *
    ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
      (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) * R)
  field_simp [hA, hB]
  ring

private theorem vector_card_real_inline_ShortcodeFiberConditioning (n : ℕ) :
    (Fintype.card (Vector n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Shortcode.Vector, F2]

private theorem binary_zero_mass_nonneg_inline_ShortcodeFiberConditioning (ell m : ℕ) :
    0 ≤ ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ := by
  have ha : 0 ≤ ((2 : ℝ) ^ ell)⁻¹ := by positivity
  have hb : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hb1 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pow_add, mul_inv]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hb1)]

theorem conditioned_output_fiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ ≤ η / 2)
    (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧
      η / 2 ≤ (matrixFiber f y).expect (fun M =>
        𝔼 p : {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0},
          if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := by
  obtain ⟨y, hy, hret⟩ := exists_output_fiber_factor_retention f haccept
  refine ⟨y, hy, ?_⟩
  have hmix := uniform_pair_mixture (fiberFactorRetention f y)
    (fiberFactorRetention_zero_left f y hy) (fiberFactorRetention_zero_right f y hy)
  simp only [vector_card_real_inline_ShortcodeFiberConditioning, ← mul_inv, ← pow_add] at hmix
  have hconditioned := EqualityFiber.nonzero_retention_ge_half hη hη1
    (binary_zero_mass_nonneg_inline_ShortcodeFiberConditioning ell m) hzero (hmix ▸ hret)
  apply hconditioned.trans
  apply le_of_eq
  unfold fiberFactorRetention
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr (by ext p; simp)
  intro p _
  rfl

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

namespace DFVSGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

theorem chartFiberRetention : ChartFiberRetention := by
  intro ell m _hell _hm η hη hη1 hzero f haccept
  obtain ⟨y, hnonempty, hretention⟩ :=
    conditioned_output_fiber f hη hη1 hzero haccept
  refine ⟨y, ?_, ?_⟩
  · exact Finset.image_nonempty.mpr hnonempty
  · rw [liftedFiber_retention_eq_half]
    have h : η / 2 ≤ (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := hretention
    linarith

theorem inversePrinciple_of_expansion_oai (hKMS : KMS.ExpansionPrinciple) :
    Shortcode.InversePrinciple :=
  inversePrinciple_of_expansion_and_chart hKMS chartFiberRetention

end
end DFVSGames.Inverse.ShortcodeFromGrassmann

end OAI
end

theorem solution : type_of% @OAI.DFVSGames.Inverse.ShortcodeFromGrassmann.inversePrinciple_of_expansion_oai := @OAI.DFVSGames.Inverse.ShortcodeFromGrassmann.inversePrinciple_of_expansion_oai
