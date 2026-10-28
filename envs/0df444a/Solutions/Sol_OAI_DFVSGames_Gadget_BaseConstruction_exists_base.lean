-- Prove2me | solution 1 for OAI.DFVSGames.Gadget.BaseConstruction.exists_base
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:33:35.318654+00:00
-- url     : https://prove2.me/submissions/46091550-ae5c-425f-b555-79c62f534fd9

import Mathlib
import Definitions.Def_OAIQ085D016

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ChildLifts
attribute [-instance] _root_.OAI.DFVSGames.Gadget.DescentProbability.noiseFintype _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Quadratic.finiteBlockOrientation _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

omit [Finite B] in

theorem descendant_detection_implies_parent
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    {S' : Submodule k (B →ₗ[k] k)} (L' : Lift s S')
    (sectionMap : S' →ₗ[k] S) (i : I)
    (hfamily : ∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p))
    (n : s.Noise) (hdetect : ∃ z, L'.family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 := by
  obtain ⟨z, hz⟩ := hdetect
  refine ⟨sectionMap z, ?_⟩
  simpa only [hfamily, Stage.next] using hz

end DFVSGames.Gadget

noncomputable section

open scoped BigOperators
open Module

namespace DFVSGames.Gadget.Orientation

section FiniteAction

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

omit [Fintype X] in

theorem sum_action_eq (x y : X) (h : ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) = ∑ g : G, f (g • y) := by
  obtain ⟨a, rfl⟩ := h
  symm
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun g => by simp [mul_smul])

theorem card_mul_sum_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℚ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
        ∑ y : X, ∑ g : G, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : G, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_action_eq x y (transitive y) f
    _ = ∑ g : G, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : G, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
    _ = (Fintype.card G : ℚ) * (∑ y : X, f y) := by simp

theorem mean_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) / Fintype.card G =
      (∑ y : X, f y) / Fintype.card X := by
  have : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hG hX).2
  simpa [mul_comm] using card_mul_sum_action x transitive f

end FiniteAction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

theorem exists_map_eq_of_finrank_eq (E F : Submodule K V)
    (h : finrank K E = finrank K F) :
    ∃ a : V ≃ₗ[K] V, E.map a.toLinearMap = F := by
  let e : E ≃ₗ[K] F := LinearEquiv.ofFinrankEq E F h
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ha ⟨u, hu⟩) ▸ (e ⟨u, hu⟩).property
  · intro hv
    obtain ⟨u, hu⟩ := e.surjective ⟨v, hv⟩
    refine ⟨u, u.property, ?_⟩
    exact (ha u).symm.trans (congrArg Subtype.val hu)

theorem rankSpace_transitive {r : ℕ} (E F : RankSpace K V r) :
    ∃ a : V ≃ₗ[K] V, a • E = F := by
  obtain ⟨a, ha⟩ := exists_map_eq_of_finrank_eq E.val F.val
    (E.property.trans F.property.symm)
  exact ⟨a, Subtype.ext ha⟩

theorem mean_oriented_subspace {r : ℕ} [Fintype (V ≃ₗ[K] V)]
    [Fintype (RankSpace K V r)] (E : RankSpace K V r) (f : RankSpace K V r → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • E)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ F : RankSpace K V r, f F) / Fintype.card (RankSpace K V r) :=
  mean_action E (rankSpace_transitive E) f

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

theorem mean_map_equiv [FiniteDimensional K U] (E : Submodule K B) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype (RankSpace K U (finrank K E))]
    (f : RankSpace K U (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K U (finrank K E), f F) /
        Fintype.card (RankSpace K U (finrank K E)) := by
  let E₀ : RankSpace K U (finrank K E) :=
    ⟨E.map J₀.toLinearMap, J₀.finrank_map_eq E⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • E₀) := by
    apply Fintype.sum_equiv (orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change E.map J.toLinearMap =
      (E.map J₀.toLinearMap).map (J₀.symm.trans J).toLinearMap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [hsum, Fintype.card_congr (orientationEquiv J₀)]
  exact mean_oriented_subspace E₀ f

theorem mean_dual_pullback [FiniteDimensional K B] [FiniteDimensional K U]
    (E : Submodule K (Module.Dual K U)) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)]
    [Fintype (Module.Dual K U ≃ₗ[K] Module.Dual K B)]
    [Fintype (Module.Dual K B ≃ₗ[K] Module.Dual K B)]
    [Fintype (RankSpace K (Module.Dual K B) (finrank K E))]
    (f : RankSpace K (Module.Dual K B) (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K (Module.Dual K B) (finrank K E), f F) /
        Fintype.card (RankSpace K (Module.Dual K B) (finrank K E)) := by
  let e := dualOrientationEquiv (K := K) (B := B) (U := U)
  have hsum := Fintype.sum_equiv e
    (fun J : B ≃ₗ[K] U => f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩)
    (fun J : Module.Dual K U ≃ₗ[K] Module.Dual K B =>
      f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) (fun _ => rfl)
  rw [hsum, Fintype.card_congr e]
  exact mean_map_equiv E J₀.dualMap f

end DFVSGames.Gadget.Orientation
end

noncomputable section

open scoped BigOperators

namespace DFVSGames.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_equiv_map_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton K V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton K V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

theorem nonzero_transitive (x y : {v : V // v ≠ 0}) :
    ∃ a : V ≃ₗ[K] V, a • x = y := by
  obtain ⟨a, ha⟩ := exists_equiv_map_nonzero (K := K) x.val y.val x.property y.property
  exact ⟨a, Subtype.ext ha⟩

theorem mean_oriented_nonzero [Fintype (V ≃ₗ[K] V)]
    [Fintype {x : V // x ≠ 0}] (x : {v : V // v ≠ 0})
    (f : {v : V // v ≠ 0} → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • x)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ y : {v : V // v ≠ 0}, f y) / Fintype.card {v : V // v ≠ 0} :=
  Orientation.mean_action x (nonzero_transitive x) f

theorem mean_iso_nonzero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype {u : U // u ≠ 0}] (b : B) (hb : b ≠ 0)
    (f : {u : U // u ≠ 0} → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ u : {u : U // u ≠ 0}, f u) / Fintype.card {u : U // u ≠ 0} := by
  let x : {u : U // u ≠ 0} := ⟨J₀ b, equiv_apply_ne_zero J₀ hb⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • x) := by
    apply Fintype.sum_equiv (Orientation.orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change J b = (J₀.symm.trans J) (J₀ b)
    simp
  rw [hsum, Fintype.card_congr (Orientation.orientationEquiv J₀)]
  exact mean_oriented_nonzero x f

end DFVSGames.Gadget.OrientationVectors
end

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F]

variable [CharP F 2]

variable [Algebra (ZMod 2) F]

theorem mem_U_iff_exists (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ ∃ a ∈ line v, ∃ w ∈ hyperplane v, p = (a, Q a + w) := by
  constructor
  · intro hp
    refine ⟨p.1, hp.1, p.2 + Q p.1, hp.2, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = Q p.1 + (p.2 + Q p.1)
      have h : Q p.1 + (p.2 + Q p.1) = p.2 + (Q p.1 + Q p.1) := by ac_rfl
      rw [h, vec_add_self, add_zero]
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact pair_mem_U v a w ha hw

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F]

variable [Finite F]

theorem reciprocal_card_FieldLine :
    (Nat.card (FieldLine F) : ℚ)⁻¹ =
      ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ := by
  rw [card_FieldLine]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_BlockOrientations
attribute [-instance] _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

private theorem natCard_ne_zero_inline_BlockNoise {A : Type*} [Finite A] [Zero A] :
    Nat.card {x : A // x ≠ 0} = Nat.card A - 1 := by
  classical
  let := Fintype.ofFinite A
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem natCard_line (v : Vec F) (hv : v ≠ 0) : Nat.card (line v) = Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_line v hv, pow_one]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem natCard_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Nat.card (hyperplane v) = Nat.card F ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_hyperplane v hv]

theorem natCard_U (v : Vec F) (hv : v ≠ 0) : Nat.card (U v) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (blockParametrization v).toEquiv, Nat.card_prod]
  change Nat.card (line v) * Nat.card (hyperplane v) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]
  ring

variable [Finite F]

theorem natCard_block_changes (v : Vec F) (hv : v ≠ 0) (p : Vec F × Vec F) :
    Nat.card {u : U v // blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [Nat.card_congr (changedCoordinatesEquiv v p), Nat.card_prod, natCard_ne_zero_inline_BlockNoise]
  change Nat.card (line v) * (Nat.card (hyperplane v) - 1) = _
  rw [natCard_line v hv, natCard_hyperplane v hv]

theorem natCard_nonzero_U (v : Vec F) (hv : v ≠ 0) :
    Nat.card {u : U v // u ≠ 0} = Nat.card F ^ 3 - 1 := by
  rw [natCard_ne_zero_inline_BlockNoise, natCard_U v hv]

theorem block_change_ratio (q : ℚ) (hq : 1 < q) :
    q * (q ^ 2 - 1) / (q ^ 3 - 1) = 1 - 1 / (q ^ 2 + q + 1) := by
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hq1 : q - 1 ≠ 0 := by linarith
  have hd : q ^ 2 + q + 1 ≠ 0 := by
    have hs := sq_nonneg q
    linarith
  have hc : q ^ 3 - 1 ≠ 0 := by
    have h : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by ring
    rw [h]
    exact mul_ne_zero hq1 hd
  field_simp [hc, hd] ; ring

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

theorem nonzeroBlockChangeProbability_eq_count (v : Vec F) (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      (Nat.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} : ℚ) /
      (Nat.card (NonzeroBlock v) : ℚ) := by
  classical
  have hcard :
      (Finset.univ.filter (fun u : NonzeroBlock v =>
        blockObservable (p + (u.val : Vec F × Vec F)) ≠ blockObservable p)).card =
      Fintype.card {u : U v //
        blockObservable (p + (u : Vec F × Vec F)) ≠ blockObservable p} := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (conditionedChangedEquiv v p)
  simp only [nonzeroBlockChangeProbability, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, hcard, Nat.card_eq_fintype_card]

theorem nonzeroBlockChangeProbability_eq (v : Vec F) (hv : v ≠ 0)
    (p : Vec F × Vec F) :
    nonzeroBlockChangeProbability v p =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [nonzeroBlockChangeProbability_eq_count, natCard_block_changes v hv p]
  change ((Nat.card F * (Nat.card F ^ 2 - 1) : ℕ) : ℚ) /
    (Nat.card {u : U v // u ≠ 0} : ℚ) = _
  rw [natCard_nonzero_U v hv]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqpos : 0 < Nat.card F := lt_trans Nat.zero_lt_one hq
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow 2 _ hqpos
  have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow 3 _ hqpos
  have hq' : (1 : ℚ) < Nat.card F := by exact_mod_cast hq
  simpa only [Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_sub hq3,
    Nat.cast_pow, Nat.cast_one] using block_change_ratio (Nat.card F) hq'

end

end DFVSGames.Quadratic

noncomputable section

open scoped BigOperators

namespace DFVSGames.Gadget.OrientedBlockKernel

open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

theorem mean_orientations_change (A : FieldLine F) (p : Vec F × Vec F)
    (d : Vec F) (hd : d ≠ 0) :
    (𝔼 J : BlockOrientation A, orientedBlockChange ⟨A, J⟩ p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  let : Finite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A)) := DFunLike.finite _
  let := Fintype.ofFinite (U (lineGenerator A) ≃ₗ[ZMod 2] U (lineGenerator A))
  calc
    _ = nonzeroBlockChangeProbability (lineGenerator A) p := by
      unfold nonzeroBlockChangeProbability orientedBlockChange
      simp only [Fintype.expect_eq_sum_div_card]
      exact OrientationVectors.mean_iso_nonzero (chosenBlockOrientation A) d hd
        (fun u => if blockObservable (p + (u.val : Vec F × Vec F)) ≠
          blockObservable p then 1 else 0)
    _ = _ := nonzeroBlockChangeProbability_eq _ (lineGenerator_ne_zero A) p

variable [Fintype (FieldLine F)] [Fintype (Vec F ≃ₗ[ZMod 2] Vec F)]

theorem mean_block_pairs (f : BlockOrientationIndex F → ℚ) :
    (𝔼 i : BlockOrientationIndex F, f i) =
      𝔼 A : FieldLine F, 𝔼 J : BlockOrientation A, f ⟨A, J⟩ := by
  classical
  calc
    _ = 𝔼 z : FieldLine F × (Vec F ≃ₗ[ZMod 2] Vec F),
        f ((blockOrientationIndexEquiv (F := F)).symm z) := by
      exact Fintype.expect_equiv (blockOrientationIndexEquiv (F := F)) _ _
        (fun i => by simp)
    _ = 𝔼 A : FieldLine F, 𝔼 a : Vec F ≃ₗ[ZMod 2] Vec F,
        f ⟨A, (blockOrientationEquiv A).symm a⟩ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      rfl
    _ = _ := by
      apply Finset.expect_congr rfl
      intro A _
      exact Fintype.expect_equiv (blockOrientationEquiv A).symm _ _ (fun _ => rfl)

theorem mean_oriented_block_change (p : Vec F × Vec F) (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  classical
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  simp_rw [mean_orientations_change _ p d hd]
  exact Fintype.expect_const _

theorem mean_oriented_block_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      orientedBlockChange i p d) =
      1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1) := by
  rw [Finset.expect_comm]
  simp_rw [mean_oriented_block_change _ d hd]
  exact Fintype.expect_const _

end DFVSGames.Gadget.OrientedBlockKernel
end

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
theorem trace_square (x : F) : traceBinary (x ^ 2) = traceBinary x := by
  simpa only [traceBinary, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ZMod.card] using
    Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x

theorem trace_square_mul (t c : F) :
    traceBinary (t ^ 2 * c) = traceBinary (t * squareRoot c) := by
  calc
    traceBinary (t ^ 2 * c) = traceBinary ((t * squareRoot c) ^ 2) := by
      rw [mul_pow, squareRoot_sq]
    _ = traceBinary (t * squareRoot c) := trace_square _

theorem trace_quadratic_vanish_iff (a c : F) :
    (∀ t : F, traceBinary (t * a + t ^ 2 * c) = 0) ↔ a = squareRoot c := by
  have heq (t : F) :
      traceBinary (t * a + t ^ 2 * c) = traceBinary (t * (a + squareRoot c)) := by
    rw [map_add, trace_square_mul, mul_add, map_add]
  simp_rw [heq]
  rw [trace_mul_vanish_iff, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem representTraceFamily_spec
    (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) (z : W) (y : Vec F) :
    traceBinary (dot (representTraceFamily γ z) y) = γ z y :=
  traceDualEquiv_symm_apply (γ z) y

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F]

private theorem dot_sub_right_inline_BlockTrace (v y z : Vec F) :
    dot v (y - z) = dot v y - dot v z := by
  simp [dot]
  ring

private theorem dot_single_inline_BlockTrace (v : Vec F) (i : Fin 3) (a : F) :
    dot v (Pi.single i a) = v i * a := by
  fin_cases i <;> simp [dot]

theorem annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, dot z y = 0) ↔ z ∈ line v := by
  constructor
  · intro hz
    have hv' : ∃ i : Fin 3, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hv'
    apply (mem_line_iff v z).mpr
    refine ⟨z i / v i, ?_⟩
    ext j
    have hy : Pi.single j (1 : F) - (v j / v i) • Pi.single i (1 : F) ∈
        hyperplane v := by
      rw [mem_hyperplane, dot_sub_right_inline_BlockTrace, dot_smul_right, dot_single_inline_BlockTrace, dot_single_inline_BlockTrace]
      simp [div_mul_cancel₀ _ hi]
    have hzero := hz _ hy
    rw [dot_sub_right_inline_BlockTrace, dot_smul_right, dot_single_inline_BlockTrace, dot_single_inline_BlockTrace,
      mul_one, mul_one, sub_eq_zero] at hzero
    change (z i / v i) * v j = z j
    rw [hzero]
    simp only [div_eq_mul_inv]
    ring
  · intro hz y hy
    obtain ⟨t, rfl⟩ := (mem_line_iff v z).mp hz
    rw [dot_smul_left, (mem_hyperplane v y).mp hy, mul_zero]

variable [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in

theorem trace_annihilator_hyperplane_iff_mem_line {v z : Vec F} (hv : v ≠ 0) :
    (∀ y ∈ hyperplane v, traceBinary (dot z y) = 0) ↔ z ∈ line v := by
  rw [← annihilator_hyperplane_iff_mem_line hv]
  constructor
  · intro hz y hy
    apply (trace_mul_vanish_iff (dot z y)).mp
    intro t
    have ht := hz (t • y) ((hyperplane v).smul_mem t hy)
    simpa only [dot_smul_right] using ht
  · intro hz y hy
    rw [hz y hy, map_zero]

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in

theorem dot_Q_smul (z : Vec F) (t : F) :
    dot z (Q (t • z)) = t ^ 2 * (z 0 * z 1 * z 2) := by
  change z 0 * ((t * z 1) * (t * z 2)) +
      z 1 * ((t * z 0) * (t * z 2)) +
      z 2 * ((t * z 0) * (t * z 1)) = _
  calc
    _ = (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) +
        (t ^ 2 * (z 0 * z 1 * z 2)) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

omit [Finite F] in
theorem blockCharacter_on_quadratic (g z : Vec F) (t : F) :
    blockCharacter g z (t • z, Q (t • z)) =
      traceBinary (t * dot g z + t ^ 2 * (z 0 * z 1 * z 2)) := by
  simp only [blockCharacter, dot_smul_right, dot_Q_smul]

theorem blockAnnihilates_self_iff (g z : Vec F) :
    BlockAnnihilates g z z ↔ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    apply (trace_quadratic_vanish_iff _ _).mp
    intro t
    have hm : (t • z, Q (t • z)) ∈ U z := by
      simpa only [add_zero] using pair_mem_U z (t • z) 0
        ((mem_line_iff z (t • z)).mpr ⟨t, rfl⟩) (Submodule.zero_mem _)
    simpa only [blockCharacter_on_quadratic] using h _ hm
  · intro h p hp
    obtain ⟨a, ha, w, hw, rfl⟩ := (mem_U_iff_exists z p).mp hp
    obtain ⟨t, rfl⟩ := (mem_line_iff z a).mp ha
    change traceBinary (dot g (t • z) + dot z (Q (t • z) + w)) = 0
    rw [dot_add_right, (mem_hyperplane z w).mp hw, add_zero,
      dot_smul_right, dot_Q_smul]
    exact (trace_quadratic_vanish_iff _ _).mpr h t

theorem mem_line_of_blockAnnihilates {g z v : Vec F} (hv : v ≠ 0)
    (h : BlockAnnihilates g z v) : z ∈ line v := by
  apply (trace_annihilator_hyperplane_iff_mem_line hv).mp
  intro y hy
  have hm : (0, y) ∈ U v := by
    simpa only [Q_zero, zero_add] using
      pair_mem_U v 0 y (Submodule.zero_mem _) hy
  simpa only [blockCharacter, dot_zero_right, zero_add] using h _ hm

theorem blockAnnihilates_iff {g z v : Vec F} (hv : v ≠ 0) (hz : z ≠ 0) :
    BlockAnnihilates g z v ↔
      z ∈ line v ∧ dot g z = squareRoot (z 0 * z 1 * z 2) := by
  constructor
  · intro h
    have hm := mem_line_of_blockAnnihilates hv h
    refine ⟨hm, (blockAnnihilates_self_iff g z).mp ?_⟩
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h
  · rintro ⟨hm, ha⟩
    have h := (blockAnnihilates_self_iff g z).mpr ha
    simpa only [BlockAnnihilates, U_eq_of_nonzero_mem_line hz hm] using h

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators Matrix

noncomputable section

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

theorem dot_lift_eq_alignment_mulVec (b : Basis ι R V)
    (point : E → V) (z : V → n → F) (g : V →ₗ[R] (n → F)) (e : E) :
    (∑ i, z (point e) i * g (point e) i) =
      (alignmentMatrix b point z *ᵥ (fun ij => g (b ij.2) ij.1)) e := by
  have hg : g (point e) = ∑ j, b.repr (point e) j • g (b j) := by
    calc
      g (point e) = g (∑ j, b.repr (point e) j • b j) :=
        congrArg g (b.sum_repr (point e)).symm
      _ = ∑ j, b.repr (point e) j • g (b j) := by simp only [map_sum, map_smul]
  rw [hg]
  simp only [Matrix.mulVec, dotProduct, alignmentMatrix,
    Finset.sum_apply, Algebra.smul_def, Pi.mul_apply,
    Pi.algebraMap_apply, Finset.mul_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Genericity
attribute [-instance] _root_.OAI.DFVSGames.Gadget.DescentProbability.noiseFintype _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

noncomputable section

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

theorem finrank_le_one_of_nonzero_unique
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → v = w) :
    Module.finrank R V ≤ 1 := by
  classical
  by_cases hex : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    apply finrank_le_one v
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · exact ⟨1, by simpa using h v w hv hw⟩
  · apply finrank_le_one (0 : V)
    intro w
    have hw : w = 0 := by
      by_contra hw
      exact hex ⟨w, hw⟩
    exact ⟨0, by simp [hw]⟩

theorem finrank_ker_le_one_of_nonzero_unique (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R f.ker ≤ 1 := by
  apply finrank_le_one_of_nonzero_unique
  intro v w hv hw
  apply Subtype.ext
  apply h v w
  · intro hv0
    apply hv
    exact Subtype.ext hv0
  · intro hw0
    apply hw
    exact Subtype.ext hw0
  · exact v.property
  · exact w.property

variable [Fintype V] [Fintype I] [DecidableEq I]

theorem lossIndices_subset_image (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    lossIndices f ⊆ (alignedCharacters aligned).image lineOf := by
  classical
  intro i hi
  obtain ⟨v, hv, hfv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨halign, hline⟩ := hkernel i v hv hfv
  apply Finset.mem_image.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, halign⟩, hline⟩

theorem card_lossIndices_le_card_aligned (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    (lossIndices f).card ≤ (alignedCharacters aligned).card := by
  classical
  exact (Finset.card_le_card (lossIndices_subset_image f aligned lineOf hkernel)).trans
    (Finset.card_image_le (s := alignedCharacters aligned) (f := lineOf))

theorem card_lossIndices_le (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I) (r : ℕ)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i)
    (hgeneric : (alignedCharacters aligned).card ≤ 3 * r) :
    (lossIndices f).card ≤ 3 * r :=
  (card_lossIndices_le_card_aligned f aligned lineOf hkernel).trans hgeneric

theorem card_lossIndices_le_nonzero (f : I → V →ₗ[R] W)
    (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → lineOf v = i) :
    (lossIndices f).card ≤ Fintype.card V - 1 := by
  classical
  have h := card_lossIndices_le_card_aligned f (fun _ => True) lineOf
    (fun i v hv hfv => ⟨trivial, hkernel i v hv hfv⟩)
  simpa [alignedCharacters, Finset.filter_ne'] using h

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] in

theorem blockRestriction_eq_zero_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) :
    blockRestriction S g v z = 0 ↔ BlockAnnihilates (g z) z v := by
  constructor
  · intro h p hp
    exact LinearMap.congr_fun h ⟨p, hp⟩
  · intro h
    ext p
    exact h p p.property

theorem mem_ker_blockRestriction_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) {v : Vec F} (hv : v ≠ 0)
    {z : S} (hz : z ≠ 0) :
    z ∈ (blockRestriction S g v).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  have hz' : (z : Vec F) ≠ 0 := fun h => hz (Subtype.ext h)
  rw [LinearMap.mem_ker, blockRestriction_eq_zero_iff, blockAnnihilates_iff hv hz']

theorem blockRestriction_nonzero_kernel_unique
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S)
    (z w : S) (hz : z ≠ 0) (hw : w ≠ 0)
    (hgz : blockRestriction S g v z = 0)
    (hgw : blockRestriction S g v w = 0) : z = w := by
  have hzline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v z).mp hgz)
  have hwline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v w).mp hgw)
  obtain ⟨t, ht⟩ := (mem_line_iff v z).mp hzline
  obtain ⟨s, hs⟩ := (mem_line_iff v w).mp hwline
  have hsne : s ≠ 0 := by
    intro hzero
    apply hw
    apply Subtype.ext
    simpa [hzero] using hs.symm
  apply hS.1 z w hz hw
  refine ⟨t / s, ?_⟩
  rw [← ht, ← hs, smul_smul, div_mul_cancel₀ _ hsne]

theorem finrank_ker_blockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) (blockRestriction S g v).ker ≤ 1 :=
  finrank_ker_le_one_of_nonzero_unique (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F B : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [AddCommGroup B] [Module (ZMod 2) B]

omit [Fintype F] in
theorem orientedBlockRestriction_eq_zero_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) :
    orientedBlockRestriction S g v J z = 0 ↔ blockRestriction S g v z = 0 := by
  change J.dualMap (blockRestriction S g v z) = 0 ↔ _
  constructor
  · intro h
    apply J.dualMap.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

omit [Fintype F] in
theorem ker_orientedBlockRestriction
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    (orientedBlockRestriction S g v J).ker = (blockRestriction S g v).ker := by
  ext z
  simp only [LinearMap.mem_ker, orientedBlockRestriction_eq_zero_iff]

theorem mem_ker_orientedBlockRestriction_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (J : B ≃ₗ[ZMod 2] U v)
    {z : S} (hz : z ≠ 0) :
    z ∈ (orientedBlockRestriction S g v J).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  rw [ker_orientedBlockRestriction]
  exact mem_ker_blockRestriction_iff S g hv hz

theorem finrank_ker_orientedBlockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) (J : B ≃ₗ[ZMod 2] U v) :
    Module.finrank (ZMod 2) (orientedBlockRestriction S g v J).ker ≤ 1 := by
  rw [ker_orientedBlockRestriction]
  exact finrank_ker_blockRestriction_le_one S g hv hS

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.BlockDescent

open Quadratic OrientedBlockKernel

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] in
theorem traceSpace_finrank (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Module.finrank (ZMod 2) (traceSpace S) = Module.finrank (ZMod 2) S :=
  (traceSpaceEquiv S).finrank_eq.symm

omit [CharP F 2] in
theorem traceSpaceEquiv_symm_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : traceSpace S) :
    ((traceSpaceEquiv S).symm z).val = traceDualEquiv z.val := by
  apply traceDualEquiv.symm.injective
  have h := congrArg Subtype.val ((traceSpaceEquiv S).apply_symm_apply z)
  simpa only [traceSpaceEquiv_apply_val, LinearEquiv.symm_apply_apply] using h

theorem childCharacter_comp_traceSpaceEquiv
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).comp (traceSpaceEquiv S).symm.toLinearMap =
      orientedBlockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1) i.2 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro b
  change γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 +
    ((traceSpaceEquiv S).symm z).val (i.2 b).val.2 =
      traceBinary (dot (traceLift S γ z) (i.2 b).val.1 + dot z.val (i.2 b).val.2)
  rw [map_add]
  rw [show traceBinary (dot (traceLift S γ z) (i.2 b).val.1) =
    γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 from
      representTraceFamily_spec (γ.comp (traceSpaceEquiv S).symm.toLinearMap) z _]
  rw [traceSpaceEquiv_symm_val, traceDualEquiv_apply]

theorem childCharacter_range_eq
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      (orientedBlockRestriction (traceSpace S) (traceLift S γ)
        (lineGenerator i.1) i.2).range := by
  rw [← childCharacter_comp_traceSpaceEquiv]
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)).symm

theorem childCharacter_range_eq_dual_pullback
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      ((blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1)).range).map
        i.2.dualMap.toLinearMap := by
  rw [childCharacter_range_eq]
  exact LinearMap.range_comp _ _

theorem childCharacter_rank_independent
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (J J' : BlockOrientation A) :
    Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J'⟩).range := by
  rw [childCharacter_range_eq_dual_pullback, childCharacter_range_eq_dual_pullback]
  rw [J.dualMap.finrank_map_eq, J'.dualMap.finrank_map_eq]

end

end DFVSGames.Gadget.BlockDescent

namespace DFVSGames.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

omit [FiniteDimensional k B] [Finite B] in
theorem childLift_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) (p : s.Input) :
    (childLift J hJ Q s S L i).family z p =
      L.family (childSection J hJ Q s S L i z) (Pi.single i p) :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).2 z p

omit [FiniteDimensional k B] [Finite B] in
theorem child_detection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (n : s.Noise)
    (hdetect : ∃ z, (childLift J hJ Q s S L i).family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 :=
  descendant_detection_implies_parent J hJ Q s S L _ _ i
    (childLift_spec J hJ Q s S L i) n hdetect

omit [Finite B] in
theorem child_rank_le (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Module.finrank k (childDomain J hJ Q s S L i) ≤ Module.finrank k S :=
  LinearMap.finrank_range_le _

theorem leafRank_le (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) (t : (Stage.iterate J hJ Q n).Noise) :
    leafRank J hJ Q n S L t ≤ Module.finrank k S := by
  induction n generalizing S with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih _ _ _).trans (child_rank_le J hJ Q _ S L t.1)

end DFVSGames.Gadget.Descent

namespace DFVSGames.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.DFVSGames.Quadratic.instFintypeFieldLine
attribute [local instance] OAI.DFVSGames.Quadratic.instFintypeSubtypeVecMemSubmoduleZModOfNatNat
omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem characterFieldLine_eq_of_mem {A₀ A : FieldLine F} {z : Vec F}
    (hz : z ≠ 0) (hm : z ∈ line (lineGenerator A)) :
    characterFieldLine A₀ z = A := by
  classical
  rw [characterFieldLine, dite_eq_right hz, ← Projectivization.mk_rep A]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact (mem_line_iff (lineGenerator A) z).mp hm

theorem alignedCharacters_eq_alignmentEvent
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F) :
    alignedCharacters (fun z : S =>
      dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2)) =
      alignmentEvent (fun z : S => (z : Vec F)) g
        (fun z : S => alignmentRightHandSide (z : Vec F)) := by
  classical
  ext z
  simp [alignedCharacters, alignmentEvent, alignmentRightHandSide,
    Fin.sum_univ_three, dot, mul_comm]

theorem card_loss_fieldLineRestrictions_le
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S)
    (A₀ : FieldLine F) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  classical
  apply card_lossIndices_le (fieldLineRestrictions S g J)
    (fun z : S => dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2))
    (fun z : S => characterFieldLine A₀ (z : Vec F)) (Module.finrank (ZMod 2) S)
  · intro A z hz hzero
    have hk := (mem_ker_orientedBlockRestriction_iff S g
      (lineGenerator_ne_zero A) (J A) hz).mp hzero
    refine ⟨hk.2, characterFieldLine_eq_of_mem ?_ hk.1⟩
    exact fun h => hz (Subtype.ext h)
  · rw [alignedCharacters_eq_alignmentEvent]
    exact hS.2 g

theorem card_loss_fieldLineRestrictions_le_three_rank
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    have h0 := congrFun h 0
    exact one_ne_zero h0)
  exact card_loss_fieldLineRestrictions_le S g J hS A₀

end

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Harmonic
attribute [-instance] _root_.OAI.DFVSGames.Gadget.DescentProbability.noiseFintype _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.Harmonic

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem harmonic_eq_sum (r : ℕ) :
    harmonic r = ∑ i ∈ Finset.range r, (↑(i + 1) : ℚ)⁻¹ := by
  induction r with
  | zero => simp
  | succ r ih => simp [harmonic_succ, Finset.sum_range_succ, ih]

theorem average_mono {f g : Ω → ℚ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g :=
  Finset.expect_le_expect fun ω _ => h ω

theorem average_nonneg {f : Ω → ℚ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ average f :=
  Finset.expect_nonneg fun ω _ => h ω

theorem average_add (f g : Ω → ℚ) :
    average (fun ω => f ω + g ω) = average f + average g :=
  Finset.expect_add_distrib _ _ _

theorem average_sub (f g : Ω → ℚ) :
    average (fun ω => f ω - g ω) = average f - average g :=
  Finset.expect_sub_distrib _ _ _

theorem average_mul_left (c : ℚ) (f : Ω → ℚ) :
    average (fun ω => c * f ω) = c * average f :=
  (Finset.mul_expect _ _ _).symm

theorem probability_nonneg (p : Ω → Prop) [DecidablePred p] :
    0 ≤ probability p := by
  apply average_nonneg
  intro ω
  split <;> norm_num

theorem probability_mono (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ ω, p ω → q ω) : probability p ≤ probability q := by
  apply average_mono
  intro ω
  by_cases hp : p ω
  · simp [hp, h ω hp]
  · simp only [ite_eq_right hp]
    split <;> norm_num

theorem probability_not [Nonempty Ω] (p : Ω → Prop) [DecidablePred p] :
    probability (fun ω => ¬ p ω) = 1 - probability p := by
  have he : (fun ω => if ¬ p ω then (1 : ℚ) else 0) =
      (fun ω => 1 - if p ω then (1 : ℚ) else 0) := by
    funext ω
    by_cases h : p ω <;> simp [h]
  unfold probability
  rw [he, average_sub, average_const]

theorem probability_eq_half_of_swap [Nonempty Ω]
    (p : Ω → Prop) [DecidablePred p] (e : Ω ≃ Ω)
    (hswap : ∀ ω, p (e ω) ↔ ¬ p ω) : probability p = 1 / 2 := by
  have he : probability (fun ω => ¬ p ω) = probability p := by
    apply Fintype.expect_equiv e
    intro ω
    simp only [hswap ω]
  rw [probability_not] at he
  linarith

theorem binary_character_detection_probability [AddGroup Ω]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0) :
    probability (fun ω => χ ω ≠ 0) = 1 / 2 := by
  apply probability_eq_half_of_swap _ (Equiv.addLeft v)
  intro ω
  change χ (v + ω) ≠ 0 ↔ ¬χ ω ≠ 0
  rw [map_add]
  generalize ha : χ v = a at hv ⊢
  generalize hb : χ ω = b
  fin_cases a <;> fin_cases b
  · exact (hv rfl).elim
  · exact (hv rfl).elim
  · change (1 : ZMod 2) + 0 ≠ 0 ↔ ¬ (0 : ZMod 2) ≠ 0
    decide
  · change (1 : ZMod 2) + 1 ≠ 0 ↔ ¬ (1 : ZMod 2) ≠ 0
    decide

theorem binary_family_detection_ge_half [AddGroup Ω]
    (detects : Ω → Prop) [DecidablePred detects]
    (χ : Ω →+ ZMod 2) (v : Ω) (hv : χ v ≠ 0)
    (hcontains : ∀ ω, χ ω ≠ 0 → detects ω) :
    (1 / 2 : ℚ) ≤ probability detects := by
  rw [← binary_character_detection_probability χ v hv]
  exact probability_mono _ _ hcontains

theorem harmonic_nonneg (r : ℕ) : 0 ≤ harmonic r := by
  induction r with
  | zero => simp
  | succ r ih => rw [harmonic_succ]; positivity

theorem harmonic_mono {r s : ℕ} (h : r ≤ s) : harmonic r ≤ harmonic s := by
  induction h with
  | refl => exact le_rfl
  | @step s h ih =>
    rw [harmonic_succ]
    have : (0 : ℚ) ≤ (↑(s + 1))⁻¹ := by positivity
    linarith

theorem harmonic_pos {r : ℕ} (h : 0 < r) : 0 < harmonic r := by
  have hm := harmonic_mono (r := 1) (s := r) h
  norm_num [harmonic_succ] at hm
  linarith

theorem harmonic_sub_predecessor {r : ℕ} (h : 0 < r) :
    harmonic r - harmonic (r - 1) = (r : ℚ)⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  simp [harmonic_succ]

theorem generic_drop_identity (r : ℕ) (next : Ω → ℕ) (hr : 0 < r)
    (hstep : ∀ ω, next ω = r ∨ next ω = r - 1) :
    average (fun ω => harmonic r - harmonic (next ω)) =
      (r : ℚ)⁻¹ * probability (fun ω => next ω < r) := by
  have he : (fun ω => harmonic r - harmonic (next ω)) =
      (fun ω => (r : ℚ)⁻¹ * if next ω < r then 1 else 0) := by
    funext ω
    rcases hstep ω with h | h
    · simp [h]
    · rw [h, ite_eq_left (Nat.sub_lt hr (by omega))]
      simp [harmonic_sub_predecessor hr]
  rw [he, average_mul_left]
  rfl

theorem generic_expected_drop_le (r : ℕ) (next : Ω → ℕ) (θ : ℚ)
    (hr : 0 < r) (hstep : ∀ ω, next ω = r ∨ next ω = r - 1)
    (hloss : probability (fun ω => next ω < r) ≤ 3 * r * θ) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ 3 * θ := by
  rw [generic_drop_identity r next hr hstep]
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  calc
    (r : ℚ)⁻¹ * probability (fun ω => next ω < r) ≤
        (r : ℚ)⁻¹ * (3 * r * θ) :=
      mul_le_mul_of_nonneg_left hloss (le_of_lt (inv_pos.mpr hrq))
    _ = 3 * θ := by field_simp [ne_of_gt hrq]

theorem arbitrary_expected_drop_le (r : ℕ) (next : Ω → ℕ) (p : ℚ)
    (hstep : ∀ ω, next ω ≤ r)
    (hloss : probability (fun ω => next ω < r) ≤ p) :
    average (fun ω => harmonic r - harmonic (next ω)) ≤ harmonic r * p := by
  calc
    average (fun ω => harmonic r - harmonic (next ω)) ≤
        average (fun ω => harmonic r * if next ω < r then 1 else 0) := by
      apply average_mono
      intro ω
      by_cases h : next ω < r
      · simp only [ite_eq_left h, mul_one]
        exact sub_le_self _ (harmonic_nonneg _)
      · have he : next ω = r := by have := hstep ω; omega
        simp [he]
    _ = harmonic r * probability (fun ω => next ω < r) := by
      rw [average_mul_left]
      rfl
    _ ≤ harmonic r * p := mul_le_mul_of_nonneg_left hloss (harmonic_nonneg _)

theorem badRankCoefficient_nonneg (r₀ : ℕ) : 0 ≤ badRankCoefficient r₀ := by
  exact mul_nonneg (harmonic_nonneg _) (by positivity)

theorem depth_budget (r₀ : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    4 * (depth r₀ θ : ℚ) * θ ≤ harmonic r₀ / 2 := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.floor_le (div_nonneg (harmonic_nonneg r₀) (le_of_lt hden))
  have hb := (le_div_iff₀ hden).mp hf
  change (depth r₀ θ : ℚ) * (8 * θ) ≤ harmonic r₀ at hb
  nlinarith

theorem survival_probability_ge_half_of_potential (rank : Ω → ℕ) (r₀ : ℕ)
    (hr₀ : 0 < r₀) (hterminal : ∀ ω, rank ω ≤ r₀)
    (hmean : harmonic r₀ / 2 ≤ average (fun ω => harmonic (rank ω))) :
    (1 / 2 : ℚ) ≤ probability (fun ω => 0 < rank ω) := by
  have hpoint : average (fun ω => harmonic (rank ω)) ≤
      harmonic r₀ * probability (fun ω => 0 < rank ω) := by
    calc
      average (fun ω => harmonic (rank ω)) ≤
          average (fun ω => harmonic r₀ * if 0 < rank ω then 1 else 0) := by
        apply average_mono
        intro ω
        by_cases h : 0 < rank ω
        · simpa only [ite_eq_left h, mul_one] using harmonic_mono (hterminal ω)
        · have he : rank ω = 0 := by omega
          simp [he]
      _ = harmonic r₀ * probability (fun ω => 0 < rank ω) := by
        rw [average_mul_left]
        rfl
  have hpos := harmonic_pos hr₀
  nlinarith

theorem probability_product {Ξ : Type*} [Fintype Ξ]
    (detects : Ω × Ξ → Prop) [DecidablePred detects] :
    probability detects = average (fun ω => probability (fun ξ => detects (ω, ξ))) := by
  unfold probability average
  simpa only [Finset.univ_product_univ] using
    (Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ)
      (fun z => if detects z then (1 : ℚ) else 0))

end DFVSGames.Gadget.Harmonic

namespace DFVSGames.Quadratic

open scoped BigOperators
open DFVSGames.Gadget.Harmonic

noncomputable section

private theorem exists_nonzero_kernel_of_range_rank_lt_inline_HarmonicLoss
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) V]
    (f : V →ₗ[ZMod 2] W)
    (h : Module.finrank (ZMod 2) f.range < Module.finrank (ZMod 2) V) :
    ∃ z, z ≠ 0 ∧ f z = 0 := by
  by_contra hn
  have hk : f.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    change z = 0
    by_contra hz0
    exact hn ⟨z, hz0, hz⟩
  have hdim := f.finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at hdim
  omega

private theorem probability_rank_drop_le_loss_count_inline_HarmonicLoss
    {I V W : Type*} [Fintype I] [Fintype V]
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : I → V →ₗ[ZMod 2] W) :
    probability (fun i => Module.finrank (ZMod 2) (f i).range <
        Module.finrank (ZMod 2) V) ≤
      ((lossIndices f).card : ℚ) / Fintype.card I := by
  classical
  have hsub : Finset.univ.filter (fun i =>
      Module.finrank (ZMod 2) (f i).range < Module.finrank (ZMod 2) V) ⊆
      lossIndices f := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      exists_nonzero_kernel_of_range_rank_lt_inline_HarmonicLoss (f i) (Finset.mem_filter.mp hi).2⟩
  simp only [probability, average, Finset.expect_eq_sum_div_card,
    Finset.sum_boole, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card hsub

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem fieldLineTheta_eq : fieldLineTheta F =
    ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ :=
  reciprocal_card_FieldLine

attribute [local instance] OAI.DFVSGames.Quadratic.harmonicFieldLineFintype
attribute [local instance] OAI.DFVSGames.Quadratic.harmonicSubmoduleFintype
theorem nextBlockRank_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (A : FieldLine F) : nextBlockRank S g J A ≤ Module.finrank (ZMod 2) S :=
  LinearMap.finrank_range_le _

theorem generic_nextBlockRank_dichotomy (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) (A : FieldLine F) :
    nextBlockRank S g J A = Module.finrank (ZMod 2) S ∨
      nextBlockRank S g J A = Module.finrank (ZMod 2) S - 1 := by
  have hk := finrank_ker_orientedBlockRestriction_le_one S g
    (lineGenerator_ne_zero A) hS (J A)
  have hdim := (fieldLineRestrictions S g J A).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (fieldLineRestrictions S g J A).ker ≤ 1 at hk
  unfold nextBlockRank
  omega

theorem generic_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      3 * Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count_inline_HarmonicLoss (fieldLineRestrictions S g J)
    _ ≤ (3 * (Module.finrank (ZMod 2) S : ℚ)) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_loss_fieldLineRestrictions_le_three_rank S g J hS
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem generic_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A)
    (hS : IsGeneric S) :
    average (fun A => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      DFVSGames.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤ 3 * fieldLineTheta F := by
  classical
  by_cases hr : 0 < Module.finrank (ZMod 2) S
  · exact generic_expected_drop_le _ _ _ hr
      (generic_nextBlockRank_dichotomy S g J hS)
      (generic_block_loss_probability_le S g J hS)
  · have hr0 : Module.finrank (ZMod 2) S = 0 := by omega
    have hnext : ∀ A, nextBlockRank S g J A = 0 := by
      intro A
      have := nextBlockRank_le S g J A
      omega
    simp only [hr0, hnext, DFVSGames.Gadget.Harmonic.harmonic_zero, sub_self]
    have hzero : average (fun _ : FieldLine F => (0 : ℚ)) = 0 := by
      simp [average]
    rw [hzero]
    unfold fieldLineTheta
    positivity

theorem card_loss_fieldLineRestrictions_le_nonzero
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤ Fintype.card S - 1 := by
  classical
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    exact one_ne_zero (congrFun h 0))
  apply card_lossIndices_le_nonzero (fieldLineRestrictions S g J)
    (fun z : S => characterFieldLine A₀ (z : Vec F))
  intro A z hz hzero
  have hk := (mem_ker_orientedBlockRestriction_iff S g
    (lineGenerator_ne_zero A) (J A) hz).mp hzero
  exact characterFieldLine_eq_of_mem (fun h => hz (Subtype.ext h)) hk.1

theorem arbitrary_block_loss_probability_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    probability (fun A => nextBlockRank S g J A < Module.finrank (ZMod 2) S) ≤
      2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  classical
  have hc : Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
    simpa only [ZMod.card] using Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  have hcount : (lossIndices (fieldLineRestrictions S g J)).card ≤
      2 ^ Module.finrank (ZMod 2) S :=
    (card_loss_fieldLineRestrictions_le_nonzero S g J).trans
      ((Nat.sub_le _ _).trans_eq hc)
  calc
    _ ≤ ((lossIndices (fieldLineRestrictions S g J)).card : ℚ) /
        Fintype.card (FieldLine F) :=
      probability_rank_drop_le_loss_count_inline_HarmonicLoss (fieldLineRestrictions S g J)
    _ ≤ ((2 : ℚ) ^ Module.finrank (ZMod 2) S) / Fintype.card (FieldLine F) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount
    _ = _ := by simp only [fieldLineTheta, Fintype.card_eq_nat_card, div_eq_mul_inv]

theorem arbitrary_block_harmonic_loss_le (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    average (fun A => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
      DFVSGames.Gadget.Harmonic.harmonic (nextBlockRank S g J A)) ≤
        DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) *
          2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F := by
  simpa only [mul_assoc] using arbitrary_expected_drop_le
    (Module.finrank (ZMod 2) S) (nextBlockRank S g J)
    (2 ^ Module.finrank (ZMod 2) S * fieldLineTheta F)
    (nextBlockRank_le S g J) (arbitrary_block_loss_probability_le S g J)

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.OutgoingHarmonic

open Quadratic OrientedBlockKernel BlockDescent Harmonic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.DFVSGames.Gadget.OutgoingHarmonic.harmonicVecLinearEquivFinite
attribute [local instance] OAI.DFVSGames.Gadget.OutgoingHarmonic.harmonicVecLinearEquivFintype
theorem outgoingLoss_eq_line_average
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ = average (fun A : FieldLine F =>
      DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        DFVSGames.Gadget.Harmonic.harmonic (nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A)) := by
  unfold outgoingLoss average
  rw [mean_block_pairs]
  apply Finset.expect_congr rfl
  intro A _
  let : Nonempty (BlockOrientation A) := ⟨chosenBlockOrientation A⟩
  have hrank (J : BlockOrientation A) :
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
        nextBlockRank (traceSpace S) (traceLift S γ) chosenBlockOrientation A := by
    rw [childCharacter_rank_independent S γ A J (chosenBlockOrientation A)]
    rw [childCharacter_range_eq]
    rfl
  simp_rw [hrank]
  exact Finset.expect_const Finset.univ_nonempty _

theorem generic_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (hS : IsGeneric (traceSpace S)) :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank] using
    generic_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation hS

theorem arbitrary_outgoing_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) :
    outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F := by
  rw [outgoingLoss_eq_line_average]
  simpa only [traceSpace_finrank, badRankCoefficient] using
    arbitrary_block_harmonic_loss_le (traceSpace S) (traceLift S γ) chosenBlockOrientation

theorem badRankCoefficient_mono {r s : ℕ} (h : r ≤ s) :
    badRankCoefficient r ≤ badRankCoefficient s := by
  unfold badRankCoefficient
  apply mul_le_mul (harmonic_mono h) (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) h)
  · positivity
  · exact harmonic_nonneg _

theorem outgoing_harmonic_loss_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (r₀ : ℕ)
    (hcap : Module.finrank (ZMod 2) S ≤ r₀)
    [Decidable (IsGeneric (traceSpace S))] :
    outgoingLoss S γ ≤ 3 * fieldLineTheta F +
      badRankCoefficient r₀ * fieldLineTheta F * if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  have hθ : 0 ≤ fieldLineTheta F := by unfold fieldLineTheta; positivity
  by_cases hS : IsGeneric (traceSpace S)
  · simpa only [not_true_eq_false, hS, ite_false, mul_zero, add_zero] using
      generic_outgoing_loss_le S γ hS
  · rw [ite_eq_left hS, mul_one]
    calc
      outgoingLoss S γ ≤ badRankCoefficient (Module.finrank (ZMod 2) S) * fieldLineTheta F :=
        arbitrary_outgoing_loss_le S γ
      _ ≤ badRankCoefficient r₀ * fieldLineTheta F :=
        mul_le_mul_of_nonneg_right (badRankCoefficient_mono hcap) hθ
      _ ≤ 3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F := by linarith

theorem descendant_harmonic_loss_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S) (r₀ : ℕ)
      (_hcap : Module.finrank (ZMod 2) S ≤ r₀)
      [Decidable (IsGeneric (traceSpace S))],
      average (fun i : BlockOrientationIndex F => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) -
        DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) (Descent.childDomain J hJ Q s S L i))) ≤
        3 * fieldLineTheta F + badRankCoefficient r₀ * fieldLineTheta F *
          if ¬ IsGeneric (traceSpace S) then 1 else 0 := by
  intro J hJ Q s S L r₀ hcap hdec
  exact outgoing_harmonic_loss_le S (Descent.commonGamma J hJ Q s S L) r₀ hcap

end

end DFVSGames.Gadget.OutgoingHarmonic

noncomputable section

open scoped BigOperators Classical
open Module

namespace DFVSGames.Gadget.FreshGenericity

open _root_.OAI.DFVSGames.Gadget.Orientation Quadratic BlockDescent OrientedBlockKernel

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype rankSpaceFintype

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

theorem mean_bad_rankSpace (r : ℕ) :
    (𝔼 S : RankSpace (ZMod 2) (BinaryDual (F := F)) r,
      if bad S.val then (1 : ℚ) else 0) = nongenericFraction F r := by
  calc
    _ = 𝔼 S : RankSpace (ZMod 2) (Vec F) r,
        if ¬IsGeneric S.val then (1 : ℚ) else 0 := by
      exact Fintype.expect_equiv (rankSpaceEquiv traceDualEquiv.symm r) _ _
        (fun T => by
          by_cases h : IsGeneric (traceSpace T.val)
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_true_eq_false, ite_false]
          · simp only [rankSpaceEquiv_apply, bad, traceSpace] at h ⊢
            simp only [h, not_false_eq_true, ite_true, if_true])
    _ = _ := by
      simp only [nongenericFraction, Fintype.expect_eq_sum_div_card,
        Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

variable [∀ A : FieldLine F, Fintype (BlockOrientation A)]

theorem mean_fresh_bad_at_line
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) =
      nongenericFraction F
        (finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
          (lineGenerator A)).range) := by
  let E := (blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator A)).range
  calc
    _ = 𝔼 J : BlockOrientation A,
        if bad (E.map J.dualMap.toLinearMap) then (1 : ℚ) else 0 := by
      apply Finset.expect_congr rfl
      intro J _
      rw [childCharacter_range_eq_dual_pullback]
    _ = 𝔼 T : RankSpace (ZMod 2) (BinaryDual (F := F)) (finrank (ZMod 2) E),
        if bad T.val then (1 : ℚ) else 0 := by
      simp only [Fintype.expect_eq_sum_div_card]
      exact mean_dual_pullback E (chosenBlockOrientation A)
        (fun T => if bad T.val then (1 : ℚ) else 0)
    _ = _ := mean_bad_rankSpace _

omit [(A : FieldLine F) → Fintype (BlockOrientation A)] in

theorem unoriented_rank_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F) :
    finrank (ZMod 2) (blockRestriction (traceSpace S) (traceLift S γ)
      (lineGenerator A)).range ≤ finrank (ZMod 2) S := by
  calc
    _ ≤ finrank (ZMod 2) (traceSpace S) := LinearMap.finrank_range_le _
    _ = _ := traceSpace_finrank S

theorem fresh_bad_at_line_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 J : BlockOrientation A,
      if bad (childCharacter orientedBlockLinear γ ⟨A, J⟩).range then (1 : ℚ) else 0) ≤ ε := by
  rw [mean_fresh_bad_at_line]
  exact hgeneric _ ((unoriented_rank_le S γ A).trans hS)

variable [Fintype (FieldLine F)]

theorem fresh_bad_le
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F))
    (r₀ : ℕ) (ε : ℚ) (hS : finrank (ZMod 2) S ≤ r₀)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) :
    (𝔼 i : BlockOrientationIndex F,
      if bad (childCharacter orientedBlockLinear γ i).range then (1 : ℚ) else 0) ≤ ε := by
  have : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  rw [mean_block_pairs]
  calc
    _ ≤ 𝔼 _A : FieldLine F, ε := Finset.expect_le_expect
      (fun A _ => fresh_bad_at_line_le S γ A r₀ ε hS hgeneric)
    _ = ε := Fintype.expect_const _

theorem descendant_bad_le
    [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] :
    let J := orientedBlockLinear (F := F)
    ∀ (hJ : Function.Surjective (aggregate J))
      (Q : Vec F → Vec F) (s : Stage (ZMod 2) (Vec F))
      (S : Submodule (ZMod 2) (BinaryDual (F := F)))
      (L : Lift (Stage.next J hJ Q s) S)
      (r₀ : ℕ) (ε : ℚ), finrank (ZMod 2) S ≤ r₀ →
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε) →
      (𝔼 i : BlockOrientationIndex F,
        if bad (Descent.childDomain J hJ Q s S L i) then (1 : ℚ) else 0) ≤ ε := by
  intro J hJ Q s S L r₀ ε hS hgeneric
  exact fresh_bad_le S (Descent.commonGamma J hJ Q s S L) r₀ ε hS hgeneric

end DFVSGames.Gadget.FreshGenericity
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_DescentProbability
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.DescentProbability

open Harmonic Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

omit [FiniteDimensional k B] in
theorem terminalPotential_succ (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    terminalPotential J hJ Q (n + 1) S L =
      average (fun i => terminalPotential J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold terminalPotential average
  change Finset.univ.expect (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    DFVSGames.Gadget.Harmonic.harmonic (leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2)) = _
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expected_terminal_loss
    (bad : Submodule k (B →ₗ[k] k) → Prop) [DecidablePred bad]
    (r₀ : ℕ) (C θ ε : ℚ) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hsmall : C * ε ≤ 1)
    (hstep : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      average (fun i => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) -
        DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k (childDomain J hJ Q s S L i))) ≤
          3 * θ + C * θ * if bad S then 1 else 0)
    (hfresh : ∀ (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
      (L : Lift (Stage.next J hJ Q s) S), Module.finrank k S ≤ r₀ →
      probability (fun i => bad (childDomain J hJ Q s S L i)) ≤ ε)
    (n : ℕ) (S : Submodule k (B →ₗ[k] k)) (L : Lift (Stage.iterate J hJ Q n) S)
    (hcap : Module.finrank k S ≤ r₀) :
    DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) - terminalPotential J hJ Q n S L ≤
      4 * n * θ + C * θ * if bad S then 1 else 0 := by
  induction n generalizing S with
  | zero =>
    simp only [terminalPotential_zero, sub_self, Nat.cast_zero, mul_zero, zero_mul,
      zero_add]
    split <;> simp_all [mul_nonneg]
  | succ n ih =>
    let s := Stage.iterate J hJ Q n
    let Sc := childDomain J hJ Q s S L
    let Lc := childLift J hJ Q s S L
    have hchild : average (fun i => DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k (Sc i)) -
        terminalPotential J hJ Q n (Sc i) (Lc i)) ≤
        4 * n * θ + C * θ * probability (fun i => bad (Sc i)) := by
      calc
        _ ≤ average (fun i => 4 * n * θ + C * θ * if bad (Sc i) then 1 else 0) := by
          apply average_mono
          intro i
          exact ih (Sc i) (Lc i) ((child_rank_le J hJ Q s S L i).trans hcap)
        _ = _ := by rw [average_add, average_const, average_mul_left]; rfl
    have hdrop := hstep s S L hcap
    have hbad := hfresh s S L hcap
    have hbad' := mul_le_mul_of_nonneg_left hbad (mul_nonneg hC hθ)
    have hsmall' := mul_le_mul_of_nonneg_right hsmall hθ
    rw [terminalPotential_succ]
    rw [average_sub] at hchild
    rw [average_sub, average_const] at hdrop
    change DFVSGames.Gadget.Harmonic.harmonic (Module.finrank k S) -
      average (fun i => terminalPotential J hJ Q n (Sc i) (Lc i)) ≤ _
    push_cast
    nlinarith

end DFVSGames.Gadget.DescentProbability

namespace DFVSGames.Gadget.LeafDetection

open Harmonic Descent DescentProbability

universe v

variable {B I X : Type v}
variable [AddCommGroup B] [Module (ZMod 2) B] [Finite B] [FiniteDimensional (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module (ZMod 2) X]

variable (J : I → B →ₗ[ZMod 2] X × B)
variable (hJ : Function.Surjective (aggregate J)) (Q : X → B)

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_nonneg (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    0 ≤ detectionProbability J hJ Q n S L := by
  classical
  exact probability_nonneg _

omit [FiniteDimensional (ZMod 2) B] in

theorem detectionProbability_restrict_le (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T) :
    detectionProbability J hJ Q n S (L.restrict hST) ≤
      detectionProbability J hJ Q n T L := by
  classical
  apply probability_mono
  rintro t ⟨z, hz⟩
  exact ⟨Submodule.inclusion hST z, hz⟩

omit [FiniteDimensional (ZMod 2) B] in
theorem detectionProbability_zero_of_rank_pos
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q 0) S) (hrank : 0 < Module.finrank (ZMod 2) S) :
    (1 / 2 : ℚ) ≤ detectionProbability J hJ Q 0 S L := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Nontrivial S := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨z, hz⟩ := exists_ne (0 : S)
  have hzval : z.val ≠ 0 := by
    intro he
    exact hz (Subtype.ext he)
  have hex : ∃ b : B, z.val b ≠ 0 := by
    by_contra h
    apply hzval
    ext b
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  have hagree : L.family z b = z.val b := L.agrees z b
  have hχ : L.family z b ≠ 0 := by rwa [hagree]
  change (1 / 2 : ℚ) ≤ probability (fun b : B => ∃ z : S, L.family z b ≠ 0)
  exact binary_family_detection_ge_half _ (L.family z).toAddMonoidHom b hχ
    (fun b hb => ⟨z, hb⟩)

omit [FiniteDimensional (ZMod 2) B] in
theorem survivalProbability_succ (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    survivalProbability J hJ Q (n + 1) S L =
      average (fun i => survivalProbability J hJ Q n
        (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
        (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
  unfold survivalProbability
  change probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    0 < leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2) = _
  exact probability_product _

omit [FiniteDimensional (ZMod 2) B] in
theorem average_child_detection_le (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q (n + 1)) S) :
    average (fun i => detectionProbability J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) ≤
        detectionProbability J hJ Q (n + 1) S L := by
  classical
  unfold detectionProbability
  change _ ≤ probability (fun t : I × (Stage.iterate J hJ Q n).Noise =>
    ∃ z : S, L.family z ((Stage.iterate J hJ Q (n + 1)).noise t) ≠ 0)
  rw [probability_product]
  apply average_mono
  intro i
  apply probability_mono
  intro t hdetect
  exact child_detection J hJ Q (Stage.iterate J hJ Q n) S L i t hdetect

omit [FiniteDimensional (ZMod 2) B] in
theorem half_survival_le_detection (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S) :
    (1 / 2 : ℚ) * survivalProbability J hJ Q n S L ≤
      detectionProbability J hJ Q n S L := by
  induction n generalizing S with
  | zero =>
    rw [survivalProbability_zero]
    split_ifs with hrank
    · simpa only [mul_one] using detectionProbability_zero_of_rank_pos J hJ Q S L hrank
    · simpa only [mul_zero] using detectionProbability_nonneg J hJ Q 0 S L
  | succ n ih =>
    rw [survivalProbability_succ, ← average_mul_left]
    calc
      _ ≤ average (fun i => detectionProbability J hJ Q n
          (childDomain J hJ Q (Stage.iterate J hJ Q n) S L i)
          (childLift J hJ Q (Stage.iterate J hJ Q n) S L i)) := by
        apply average_mono
        intro i
        exact ih _ _
      _ ≤ detectionProbability J hJ Q (n + 1) S L :=
        average_child_detection_le J hJ Q n S L

theorem quarter_detection_of_terminal_potential (n : ℕ)
    (S : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2))
    (L : Lift (Stage.iterate J hJ Q n) S)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S L) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n S L := by
  have hsurv : (1 / 2 : ℚ) ≤ survivalProbability J hJ Q n S L :=
    survival_probability_ge_half_of_potential (leafRank J hJ Q n S L)
      (Module.finrank (ZMod 2) S) hrank (leafRank_le J hJ Q n S L) hpotential
  have hdet := half_survival_le_detection J hJ Q n S L
  linarith

theorem quarter_detection_of_restricted_terminal_potential (n : ℕ)
    (S T : Submodule (ZMod 2) (B →ₗ[ZMod 2] ZMod 2)) (hST : S ≤ T)
    (L : Lift (Stage.iterate J hJ Q n) T)
    (hrank : 0 < Module.finrank (ZMod 2) S)
    (hpotential : DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q n S (L.restrict hST)) :
    (1 / 4 : ℚ) ≤ detectionProbability J hJ Q n T L :=
  (quarter_detection_of_terminal_potential J hJ Q n S (L.restrict hST)
    hrank hpotential).trans (detectionProbability_restrict_le J hJ Q n S T hST L)

end DFVSGames.Gadget.LeafDetection

namespace DFVSGames.Gadget.BaseDetection

open Quadratic OrientedBlockKernel BlockDescent Harmonic
open Descent DescentProbability LeafDetection
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)]

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] in
theorem traceSpace_logicalCharacters (S : Submodule (ZMod 2) (Vec F)) :
    traceSpace (logicalCharacters S) = S := by
  exact (Submodule.map_symm_eq_iff traceDualEquiv).mpr rfl

omit [CharP F 2] [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] in
theorem logicalCharacters_finrank (S : Submodule (ZMod 2) (Vec F)) :
    Module.finrank (ZMod 2) (logicalCharacters S) = Module.finrank (ZMod 2) S :=
  traceDualEquiv.finrank_map_eq S

omit [CharP F 2] [Algebra (ZMod 2) F] [DecidableEq (BlockOrientationIndex F)] [Nonempty (BlockOrientationIndex F)] in
theorem theta_pos : 0 < fieldLineTheta F := by
  have hc : (0 : ℚ) < Nat.card (FieldLine F) := by
    exact_mod_cast (card_FieldLine_pos (F := F))
  exact inv_pos.mpr hc

theorem full_lift_detection :
    let J : BlockOrientationIndex F → Vec F →ₗ[ZMod 2] Vec F × Vec F :=
      orientedBlockLinear
    ∀ (hJ : Function.Surjective (aggregate J))
      (r₀ : ℕ) (ε : ℚ) (_hr₀ : 0 < r₀)
      (_hbudget : badRankCoefficient r₀ * ε ≤ 1)
      (_hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
      (S₀ : Submodule (ZMod 2) (Vec F))
      (_hrank : Module.finrank (ZMod 2) S₀ = r₀) (_hS₀ : IsGeneric S₀)
      (L : Lift (Stage.iterate J hJ Q (depth r₀ (fieldLineTheta F)))
        (⊤ : Submodule (ZMod 2) (BinaryDual (F := F)))),
      (1 / 4 : ℚ) ≤ detectionProbability J hJ Q
        (depth r₀ (fieldLineTheta F)) ⊤ L := by
  intro J hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  classical
  let S := logicalCharacters S₀
  have hSrank : Module.finrank (ZMod 2) S = r₀ :=
    (logicalCharacters_finrank S₀).trans hrank
  have hSgeneric : IsGeneric (traceSpace S) := by
    simpa only [S, traceSpace_logicalCharacters] using hS₀
  let L₀ := L.restrict (show S ≤ ⊤ from le_top)
  have hdrop := DescentProbability.expected_terminal_loss J hJ Q
    (fun T => ¬ IsGeneric (traceSpace T)) r₀ (badRankCoefficient r₀)
    (fieldLineTheta F) ε (badRankCoefficient_nonneg r₀) (le_of_lt theta_pos) hbudget
    (by
      intro s T L' hT
      exact OutgoingHarmonic.descendant_harmonic_loss_le hJ Q s T L' r₀ hT)
    (by
      intro s T L' hT
      have hf := FreshGenericity.descendant_bad_le hJ Q s T L' r₀ ε hT hgeneric
      refine (le_of_eq ?_).trans hf
      apply Finset.expect_congr rfl
      intro i _
      by_cases hi : IsGeneric (traceSpace (childDomain J hJ Q s T L' i))
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_true_eq_false, ite_false]
      · simp only [FreshGenericity.bad, J] at hi ⊢
        simp only [hi, not_false_eq_true, ite_true, if_true])
    (depth r₀ (fieldLineTheta F)) S L₀ hSrank.le
  have hdepth := depth_budget r₀ (fieldLineTheta F) theta_pos
  have hpotential : DFVSGames.Gadget.Harmonic.harmonic (Module.finrank (ZMod 2) S) / 2 ≤
      terminalPotential J hJ Q (depth r₀ (fieldLineTheta F)) S L₀ := by
    simp only [hSgeneric, not_true_eq_false, ite_false, mul_zero, add_zero, hSrank] at hdrop ⊢
    linarith
  exact quarter_detection_of_restricted_terminal_potential J hJ Q
    (depth r₀ (fieldLineTheta F)) S ⊤ le_top L (hSrank.symm ▸ hr₀) hpotential

end

end DFVSGames.Gadget.BaseDetection

namespace DFVSGames.Gadget.Quotient

variable {𝕜 P B : Type*} [Ring 𝕜]
variable [AddCommGroup P] [Module 𝕜 P] [AddCommGroup B] [Module 𝕜 B]

theorem change_iff (R : Submodule 𝕜 P) (lam : R →ₗ[𝕜] B)
    (C : P → B) (hC : Equivariant R lam C) (u a : P) :
    (output R lam C hC (projection R lam u + projection R lam a) ≠
      output R lam C hC (projection R lam u)) ↔ C (u + a) ≠ C u := by
  rw [← map_add, output_projection, output_projection]

end DFVSGames.Gadget.Quotient

namespace DFVSGames.Gadget.StageQuotient

universe u v

variable {k : Type u} {B : Type v} [CommRing k]
variable [AddCommGroup B] [Module k B]

theorem noise_change_iff (s : Stage k B) (u : s.Input) (t : s.Noise) :
    (output s (projection s u + noise s t) ≠ output s (projection s u)) ↔
      s.output (u + s.noise t) ≠ s.output u :=
  Quotient.change_iff (shifts s) (logical s) s.output (equivariant s) u (s.noise t)

end DFVSGames.Gadget.StageQuotient

namespace DFVSGames.Gadget.DetectionBridge

open Harmonic

variable {K B V E Ω : Type*} [Field K]
variable [AddCommGroup B] [Module K B] [AddCommGroup V] [Module K V]
variable [AddCommGroup E] [Module K E] [Fintype Ω]

theorem exists_leftInverse_of_logical_injective (ι : B →ₗ[K] V)
    (T : V →ₗ[K] E) (hinjective : Function.Injective (T.comp ι)) :
    ∃ l : E →ₗ[K] B, l.comp (T.comp ι) = LinearMap.id :=
  (T.comp ι).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinjective)

theorem fullLift_of_leftInverse (ι : B →ₗ[K] V) (T : V →ₗ[K] E)
    (l : E →ₗ[K] B) (hleft : l.comp (T.comp ι) = LinearMap.id) :
    IsFullLift ι (l.comp T).dualMap := by
  intro z b
  change z (l (T (ι b))) = z b
  have hb : l (T (ι b)) = b := LinearMap.congr_fun hleft b
  rw [hb]

theorem target_detection_of_full_lift_bound [DecidableEq E]
    (noise : Ω → V) (ι : B →ₗ[K] V) (T : V →ₗ[K] E) (q : ℚ)
    (hfull : ∀ ψ : Module.Dual K B →ₗ[K] Module.Dual K V,
      IsFullLift ι ψ → q ≤ characterDetection noise ψ)
    (hinjective : Function.Injective (T.comp ι)) :
    q ≤ probability (fun ω => T (noise ω) ≠ 0) := by
  classical
  obtain ⟨l, hl⟩ := exists_leftInverse_of_logical_injective ι T hinjective
  calc
    q ≤ characterDetection noise (l.comp T).dualMap :=
      hfull _ (fullLift_of_leftInverse ι T l hl)
    _ ≤ probability (fun ω => T (noise ω) ≠ 0) := by
      unfold characterDetection
      apply probability_mono
      rintro ω ⟨z, hz⟩ hzero
      apply hz
      change z (l (T (noise ω))) = 0
      simp [hzero]

end DFVSGames.Gadget.DetectionBridge

namespace DFVSGames.Gadget.QuotientDetection

open Harmonic DetectionBridge
open scoped Classical

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

omit [Finite B] in
theorem pullback_detection_iff (s : Stage k B)
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) (n : s.Noise) :
    (∃ z, (pullbackFullLift s ψ hψ).family z (s.noise n) ≠ 0) ↔
      ∃ z, ψ z (StageQuotient.noise s n) ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.val, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨⟨z, Submodule.mem_top⟩, hz⟩

omit [Finite B] in

theorem full_detection_after_quotient (s : Stage k B) [Fintype s.Noise] (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (ψ : Module.Dual k B →ₗ[k] Module.Dual k (StageQuotient.Space s))
    (hψ : IsFullLift (StageQuotient.shift s) ψ) :
    q ≤ characterDetection (StageQuotient.noise s) ψ := by
  classical
  have h := hfull (pullbackFullLift s ψ hψ)
  simpa only [characterDetection, pullback_detection_iff] using h

omit [Finite B] in
theorem target_detection_after_quotient (s : Stage k B) [Fintype s.Noise]
    {E : Type*} [AddCommGroup E] [Module k E] [DecidableEq E]
    (T : StageQuotient.Space s →ₗ[k] E) (q : ℚ)
    (hfull : ∀ L : Lift s (⊤ : Submodule k (Module.Dual k B)),
      q ≤ probability (fun n => ∃ z, L.family z (s.noise n) ≠ 0))
    (hinj : Function.Injective (T.comp (StageQuotient.shift s))) :
    q ≤ probability (fun n => T (StageQuotient.noise s n) ≠ 0) := by
  exact target_detection_of_full_lift_bound (StageQuotient.noise s)
    (StageQuotient.shift s) T q (full_detection_after_quotient s q hfull) hinj

end DFVSGames.Gadget.QuotientDetection

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_NonlinearRecurrence
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Gadget.EmbeddedConditional

open scoped BigOperators

variable {k P R B Z M : Type*} [Ring k]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup B] [Module k B] [Fintype B]
variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_uniform_output_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (D : P → Z) (hD : ∀ u h, D (u + e h) = D u)
    (f : B → Z → M) :
    (𝔼 u, f (C u) (D u)) = 𝔼 u, 𝔼 b : B, f b (D u) := by
  classical
  have hs (b : B) :
      (𝔼 u, f (C u + b) (D u)) = 𝔼 u, f (C u) (D u) := by
    obtain ⟨h, rfl⟩ := hlam b
    apply Fintype.expect_equiv (Equiv.addRight (e h))
    intro u
    simp only [Equiv.coe_addRight, hC, hD]
  calc
    (𝔼 u, f (C u) (D u)) = 𝔼 b : B, 𝔼 u, f (C u + b) (D u) := by
      simp only [hs, Fintype.expect_const]
    _ = 𝔼 u, 𝔼 b : B, f (C u + b) (D u) := Finset.expect_comm _ _ _
    _ = 𝔼 u, 𝔼 b : B, f b (D u) := by
      apply Finset.expect_congr rfl
      intro u _
      apply Fintype.expect_equiv (Equiv.addLeft (C u))
      intro b
      rfl

theorem expect_equivariant_output (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (f : B → M) :
    (𝔼 u, f (C u)) = 𝔼 b : B, f b := by
  have he := expect_uniform_output_embedded e lam hlam C hC
    (fun _ => ()) (fun _ _ => rfl) (fun b _ => f b)
  simpa only [Fintype.expect_const] using he

theorem expect_linear_surjective (f : P →ₗ[k] B) (hf : Function.Surjective f)
    (test : B → M) : (𝔼 u, test (f u)) = 𝔼 b : B, test b := by
  apply expect_equivariant_output (LinearMap.id : P →ₗ[k] P) f hf f
  intro u h
  exact f.map_add u h

end DFVSGames.Gadget.EmbeddedConditional

namespace DFVSGames.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem compLeft_surjective (lam : R →ₗ[k] B) (hlam : Function.Surjective lam) :
    Function.Surjective (lam.compLeft I) := by
  intro b
  choose h hh using fun i => hlam (b i)
  exact ⟨h, funext hh⟩

omit [Fintype X] [Fintype B] [DecidableEq B] in
theorem aggregate_single (J : I → B →ₗ[k] X × B) (i : I) (b : B) :
    aggregate J (Pi.single i b) = J i b := by
  classical
  change (∑ j, J j ((Pi.single i b : I → B) j)) = J i b
  simp only [LinearMap.apply_single]
  simp

omit [Fintype I] [Fintype P] [Fintype B] [DecidableEq B] in
theorem child_outputs_perturb (C : P → B) (u : I → P) (i : I) (a : P) :
    (fun j => C ((u + (Pi.single i a : I → P)) j)) =
      (fun j => C (u j)) + (Pi.single i (C (u i + a) - C (u i)) : I → B) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [add_comm (C (u i)), sub_add_cancel]
  · simp [Pi.single_eq_of_ne hj]

omit [Module k P] in
omit [Fintype P] [Fintype X] [Fintype B] [DecidableEq B] in
theorem parent_output_perturb (J : I → B →ₗ[k] X × B) (C : P → B)
    (F : X × B → B) (u : I → P) (i : I) (a : P) :
    F (aggregate J (fun j => C ((u + (Pi.single i a : I → P)) j))) =
      F (aggregate J (fun j => C (u j)) + J i (C (u i + a) - C (u i))) := by
  rw [child_outputs_perturb, map_add, aggregate_single]

theorem expect_change_at_index (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (i : I) (a : P) :
    (𝔼 u : I → P,
      change F (aggregate J (fun j => C (u j))) (J i (C (u i + a) - C (u i)))) =
      𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
  have hCt : ∀ (u : I → P) (h : I → R),
      (fun j => C ((u + (e.compLeft I) h) j)) =
        (fun j => C (u j)) + (lam.compLeft I) h := by
    intro u h
    funext j
    exact hC (u j) (h j)
  have hDt : ∀ (u : I → P) (h : I → R),
      C ((u + (e.compLeft I) h) i + a) - C ((u + (e.compLeft I) h) i) =
        C (u i + a) - C (u i) := by
    intro u h
    change C (u i + e (h i) + a) - C (u i + e (h i)) = _
    have he : u i + e (h i) + a = (u i + a) + e (h i) := by
      simp only [add_assoc, add_comm (e (h i)) a]
    rw [he, hC, hC, add_sub_add_right_eq_sub]
  calc
    _ = 𝔼 u : I → P, 𝔼 b : I → B,
        change F (aggregate J b) (J i (C (u i + a) - C (u i))) :=
      EmbeddedConditional.expect_uniform_output_embedded
        (e.compLeft I) (lam.compLeft I) (compLeft_surjective lam hlam)
        (fun u j => C (u j)) hCt (fun u => C (u i + a) - C (u i)) hDt
        (fun b d => change F (aggregate J b) (J i d))
    _ = 𝔼 u : I → P, 𝔼 z : X × B,
        change F z (J i (C (u i + a) - C (u i))) := by
      apply Finset.expect_congr rfl
      intro u _
      exact EmbeddedConditional.expect_linear_surjective (aggregate J) hJ
        (fun z => change F z (J i (C (u i + a) - C (u i))))
    _ = 𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
      exact EmbeddedConditional.expect_linear_surjective
        (LinearMap.proj i : (I → P) →ₗ[k] P)
        (fun x => ⟨fun _ => x, rfl⟩)
        (fun x : P => 𝔼 z : X × B, change F z (J i (C (x + a) - C x)))

omit [DecidableEq I] in

theorem kernel_all (J : I → B →ₗ[k] X × B) (F : X × B → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ)
    (d : B) :
    (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ * (if d ≠ 0 then 1 else 0) := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  · simp only [ite_eq_left hd, mul_one]
    exact hk d hd

theorem parent_change_recurrence {N : Type*} [Fintype N]
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (C : P → B) (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (noise : N → P) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ) :
    (𝔼 i, 𝔼 n : N, 𝔼 u : I → P,
      if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
        F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
      ρ * (𝔼 n : N, 𝔼 x : P, if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
  classical
  have hpoint (i : I) (n : N) :
      (𝔼 u : I → P,
        if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
          F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
        𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
    simp_rw [parent_output_perturb]
    exact expect_change_at_index J hJ e lam hlam C hC F i (noise n)
  simp_rw [hpoint]
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 n : N, 𝔼 x : P, 𝔼 i,
        𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
      apply Finset.expect_congr rfl
      intro n _
      exact Finset.expect_comm _ _ _
    _ = 𝔼 n : N, 𝔼 x : P,
        ρ * (if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      apply Finset.expect_congr rfl
      intro x _
      simpa only [ne_eq, sub_eq_zero] using kernel_all J F ρ hk (C (x + noise n) - C x)
    _ = _ := by simp only [← Finset.mul_expect]

end DFVSGames.Gadget.NonlinearRecurrence

namespace DFVSGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

theorem average_eq_expect {A : Type*} [Fintype A] (f : A → ℚ) :
    average f = 𝔼 a, f a := by
  have he : Fintype.ofFinite A = ‹Fintype A› := Subsingleton.elim _ _
  unfold average
  rw [he]

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

theorem error_eq_expect [DecidableEq B] (s : Stage k B) [Fintype s.Input] [Fintype s.Noise] :
    error s = 𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0 := by
  classical
  simp only [error, average_eq_expect]
  apply Finset.expect_congr rfl
  intro n _
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

variable [Fintype B] [DecidableEq B]

theorem base_error : error (Stage.base (k := k) (B := B)) =
    1 - 1 / (Fintype.card B : ℚ) := by
  classical
  let : Fintype (Stage.base (k := k) (B := B)).Input := ‹Fintype B›
  let : Fintype (Stage.base (k := k) (B := B)).Noise := ‹Fintype B›
  rw [error_eq_expect]
  change (𝔼 a : B, 𝔼 u : B, if u + a ≠ u then (1 : ℚ) else 0) = _
  have hpoint (a u : B) : (u + a ≠ u) ↔ a ≠ 0 := by
    constructor
    · intro h ha
      exact h (by rw [ha, add_zero])
    · intro ha h
      apply ha
      exact add_left_cancel (show u + a = u + 0 by simpa only [add_zero] using h)
  simp_rw [hpoint, Fintype.expect_const]
  calc
    (𝔼 a : B, if a ≠ 0 then (1 : ℚ) else 0) =
        𝔼 a : B, (1 - if a = 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    _ = 1 - (𝔼 a : B, if a = 0 then (1 : ℚ) else 0) := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
    _ = _ := by simp []

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X] [Fintype X]

theorem next_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (s : Stage k B) : error (Stage.next J hJ Q s) = ρ * error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let : Fintype (Stage.next J hJ Q s).Input := inferInstanceAs (Fintype (I → s.Input))
  let : Fintype (Stage.next J hJ Q s).Noise := inferInstanceAs (Fintype (I × s.Noise))
  simp only [error_eq_expect]
  change (𝔼 t : I × s.Noise, 𝔼 u : I → s.Input,
    if parentOutput J s.output Q (u + (Pi.single t.1 (s.noise t.2) : I → s.Input)) ≠
      parentOutput J s.output Q u then (1 : ℚ) else 0) =
    ρ * (𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0)
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact NonlinearRecurrence.parent_change_recurrence J hJ s.embed s.logical
    s.logical_surjective s.output s.equivariant (fun p => p.2 + Q p.1) s.noise ρ hk

theorem iterate_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (n : ℕ) : error (Stage.iterate J hJ Q n) =
      (1 - 1 / (Fintype.card B : ℚ)) * ρ ^ n := by
  induction n with
  | zero => simp [Stage.iterate_zero, base_error]
  | succ n ih =>
    rw [Stage.iterate_succ, next_error J hJ Q ρ hk, ih, pow_succ]
    ac_rfl

theorem quotient_error (s : Stage k B) : error (StageQuotient.toStage s) = error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let := Fintype.ofFinite (StageQuotient.Space s)
  let : Fintype (StageQuotient.toStage s).Input := inferInstanceAs (Fintype (StageQuotient.Space s))
  let : Fintype (StageQuotient.toStage s).Noise := inferInstanceAs (Fintype s.Noise)
  simp only [error_eq_expect]
  change (𝔼 n : s.Noise, 𝔼 x : StageQuotient.Space s,
    if StageQuotient.output s (x + StageQuotient.noise s n) ≠
      StageQuotient.output s x then (1 : ℚ) else 0) =
    𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0
  apply Finset.expect_congr rfl
  intro n _
  calc
    _ = 𝔼 u : s.Input,
      if StageQuotient.output s (StageQuotient.projection s u + StageQuotient.noise s n) ≠
        StageQuotient.output s (StageQuotient.projection s u) then (1 : ℚ) else 0 :=
      (EmbeddedConditional.expect_linear_surjective (StageQuotient.projection s)
        (StageQuotient.projection_surjective s)
        (fun x : StageQuotient.Space s =>
          if StageQuotient.output s (x + StageQuotient.noise s n) ≠
            StageQuotient.output s x then (1 : ℚ) else 0)).symm
    _ = _ := by simp only [StageQuotient.noise_change_iff]

end DFVSGames.Gadget.StageNoiseRecurrence

noncomputable section

namespace DFVSGames.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.DFVSGames.Gadget.QuadraticStageNoise.indexDecidableEq
attribute [local instance] OAI.DFVSGames.Gadget.QuadraticStageNoise.automorphismFinite
attribute [local instance] OAI.DFVSGames.Gadget.QuadraticStageNoise.automorphismFintype
attribute [local instance] OAI.DFVSGames.Gadget.QuadraticStageNoise.indexNonempty
theorem actual_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      NonlinearRecurrence.change (fun z => z.2 + Q z.1) p (blockEmbedding i d)) =
      rate F := by
  classical
  exact OrientedBlockKernel.mean_oriented_block_kernel d hd

theorem stage_error (n : ℕ) :
    StageNoiseRecurrence.error (stage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  have he := StageNoiseRecurrence.iterate_error (blockEmbedding (F := F))
    aggregate_blockEmbedding_surjective Q (rate F) actual_kernel n
  simpa only [stage, Vec, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.card_eq_fintype_card] using he

theorem quotientStage_error (n : ℕ) :
    StageNoiseRecurrence.error (quotientStage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  rw [quotientStage, StageNoiseRecurrence.quotient_error, stage_error]

end DFVSGames.Gadget.QuadraticStageNoise
end

namespace DFVSGames.Gadget.Parameters

open Harmonic
open scoped BigOperators

theorem harmonic_double (n : ℕ) (hn : 0 < n) :
    DFVSGames.Gadget.Harmonic.harmonic n + 1 / 2 ≤ DFVSGames.Gadget.Harmonic.harmonic (2 * n) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hsplit : DFVSGames.Gadget.Harmonic.harmonic (2 * n) = DFVSGames.Gadget.Harmonic.harmonic n +
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    rw [harmonic_eq_sum, show 2 * n = n + n by omega, Finset.sum_range_add]
    rw [← harmonic_eq_sum n]
  have hs : (∑ _i ∈ Finset.range n, (2 * (n : ℚ))⁻¹) ≤
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply inv_anti₀ (by positivity)
    exact_mod_cast (show n + i + 1 ≤ 2 * n by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have he : (n : ℚ) * (2 * (n : ℚ))⁻¹ = 1 / 2 := by
    field_simp [ne_of_gt hnq]
  rw [he] at hs
  rw [hsplit]
  linarith

theorem harmonic_pow_two (k : ℕ) : (k : ℚ) / 2 ≤ DFVSGames.Gadget.Harmonic.harmonic (2 ^ k) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_div, pow_zero] using harmonic_nonneg 1
  | succ k ih =>
    have hd := harmonic_double (2 ^ k) (pow_pos (by decide) _)
    rw [pow_succ, Nat.mul_comm]
    push_cast
    linarith

theorem rankFor_pos (level : ℚ) : 0 < rankFor level := by
  unfold rankFor
  positivity

theorem le_harmonic_rankFor (level : ℚ) : level ≤ DFVSGames.Gadget.Harmonic.harmonic (rankFor level) := by
  have hc := Nat.le_ceil (2 * level)
  have hh := harmonic_pow_two ⌈2 * level⌉₊
  change level ≤ DFVSGames.Gadget.Harmonic.harmonic (2 ^ ⌈2 * level⌉₊)
  linarith

theorem genericityError_pos (r₀ : ℕ) : 0 < genericityError r₀ := by
  unfold genericityError
  have := badRankCoefficient_nonneg r₀
  positivity

theorem genericityError_lt_one (r₀ : ℕ) : genericityError r₀ < 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem genericityError_budget (r₀ : ℕ) :
    badRankCoefficient r₀ * genericityError r₀ ≤ 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  rw [← mul_div_assoc, mul_one]
  apply (div_le_one (by positivity)).mpr
  linarith

theorem geometric_reciprocal_bound (θ : ℚ) (_hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (n : ℕ) : (1 - θ) ^ n * (1 + (n : ℚ) * θ) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 ≤ (1 - θ) ^ n := pow_nonneg (sub_nonneg.mpr hθone) _
    have hn : (0 : ℚ) ≤ n := by positivity
    have hstep : (1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ) ≤
        1 + (n : ℚ) * θ := by
      push_cast
      nlinarith [sq_nonneg θ, mul_nonneg hn (sq_nonneg θ)]
    calc
      (1 - θ) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℚ) * θ) =
          (1 - θ) ^ n * ((1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ)) := by
        rw [pow_succ]
        ring
      _ ≤ (1 - θ) ^ n * (1 + (n : ℚ) * θ) :=
        mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

theorem geometric_at_depth_le (p θ : ℚ) (r₀ : ℕ) (hp : 0 < p)
    (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hlarge : 8 * (p⁻¹ + 1) ≤ DFVSGames.Gadget.Harmonic.harmonic r₀) :
    (1 - θ) ^ depth r₀ θ ≤ p := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.lt_floor_add_one (DFVSGames.Gadget.Harmonic.harmonic r₀ / (8 * θ))
  have hf' := (div_lt_iff₀ hden).mp hf
  change DFVSGames.Gadget.Harmonic.harmonic r₀ < ((depth r₀ θ : ℚ) + 1) * (8 * θ) at hf'
  have hnθ : p⁻¹ ≤ (depth r₀ θ : ℚ) * θ := by nlinarith
  have hpne : p ≠ 0 := ne_of_gt hp
  have hm := mul_le_mul_of_nonneg_left hnθ (le_of_lt hp)
  simp only [mul_inv_cancel₀ hpne] at hm
  have hr := geometric_reciprocal_bound θ (le_of_lt hθ) hθone (depth r₀ θ)
  have hb : 1 ≤ p * (1 + (depth r₀ θ : ℚ) * θ) := by nlinarith
  have hpositive : 0 < 1 + (depth r₀ θ : ℚ) * θ := by positivity
  exact (mul_le_mul_iff_left₀ hpositive).mp (by simpa only [mul_comm] using hr.trans hb)

theorem initialRank_pos (p : ℚ) : 0 < initialRank p := rankFor_pos _

theorem initialRank_large (p : ℚ) :
    8 * (p⁻¹ + 1) ≤ DFVSGames.Gadget.Harmonic.harmonic (initialRank p) := le_harmonic_rankFor _

theorem effective_parameters (p : ℚ) (hp : 0 < p) :
    ∃ r₀ : ℕ, ∃ ε : ℚ,
      0 < r₀ ∧ 0 < ε ∧ ε < 1 ∧ badRankCoefficient r₀ * ε ≤ 1 ∧
      ∀ θ : ℚ, 0 < θ → θ ≤ 1 → (1 - θ) ^ depth r₀ θ ≤ p := by
  refine ⟨initialRank p, genericityError (initialRank p), initialRank_pos p,
    genericityError_pos _, genericityError_lt_one _, genericityError_budget _, ?_⟩
  intro θ hθ hθone
  exact geometric_at_depth_le p θ (initialRank p) hp hθ hθone (initialRank_large p)

end DFVSGames.Gadget.Parameters

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

theorem coeff_expand_mul_monomial_of_ne
    (p : MvPolynomial σ R) (a b n : σ →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) (hab : a ≠ b) :
    (expand 2 p * monomial b 1).coeff (2 • n + a) = 0 := by
  classical
  rw [coeff_mul_monomial']
  split_ifs with hle
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h
      push Not at h
      exact hab (Finsupp.ext h)
    have hcoeff : (expand 2 p).coeff (2 • n + a - b) = 0 := by
      apply coeff_expand_of_not_dvd (i := k)
      intro hdiv
      obtain ⟨m, hm⟩ := hdiv
      have hle' := hle k
      have ha' := ha k
      have hb' := hb k
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul] at hm hle'
      omega
    simp [hcoeff]
  · rfl

theorem coeff_expand_mul_monomial_self
    (p : MvPolynomial σ R) (a n : σ →₀ ℕ) :
    (expand 2 p * monomial a 1).coeff (2 • n + a) = p.coeff n := by
  rw [coeff_mul_monomial, coeff_expand_smul 2 (by decide), mul_one]

theorem coeff_sum_expand_mul_monomial [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R)
    (i : ι) (n : σ →₀ ℕ) :
    (∑ j, expand 2 (p j) * monomial (e j) 1).coeff (2 • n + e i) =
      (p i).coeff n := by
  classical
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · exact coeff_expand_mul_monomial_self _ _ _
  · intro j _ hji
    exact coeff_expand_mul_monomial_of_ne _ _ _ _ (he i) (he j)
      (fun h => hji (hinj h).symm)
  · simp

theorem sum_expand_mul_monomial_eq_zero_iff [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R) :
    (∑ i, expand 2 (p i) * monomial (e i) 1) = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h i
    ext n
    have hc := congrArg (fun q : MvPolynomial σ R => q.coeff (2 • n + e i)) h
    simpa only [coeff_sum_expand_mul_monomial e he hinj, MvPolynomial.coeff_zero] using hc
  · intro h
    simp [h]

theorem blockExponent_squarefree {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : SquarefreeExponent (blockExponent v) := by
  classical
  intro x
  simp only [blockExponent_apply]
  split_ifs <;> decide

theorem blockExponent_injective {κ J : Type*} [Finite κ] [Finite J] :
    Function.Injective (blockExponent (κ := κ) (J := J)) := by
  classical
  intro v w h
  funext i
  have hc := congrArg (fun e : (κ × J) →₀ ℕ => e (i, v i)) h
  by_contra hne
  simp [hne] at hc

theorem blockExponent_eq_sum {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    blockExponent v = ∑ i, Finsupp.single (i, v i) 1 := by
  classical
  ext x
  rw [blockExponent_apply, Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single x.1]
  · simp [Finsupp.single_apply, Prod.ext_iff, eq_comm]
  · intro i _ hi
    have hix : (i, v i) ≠ x := fun h => hi (congrArg Prod.fst h)
    simp [hix]
  · simp

theorem monomial_blockExponent {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    (monomial (blockExponent v) 1 : MvPolynomial (κ × J) R) =
      ∏ i, X (i, v i) := by
  rw [blockExponent_eq_sum, monomial_sum_one]
  rfl

theorem sum_expand_mul_blockMonomial_eq_zero_iff {J : Type*} [Fintype J]
    (p : (Fin 3 → J) → MvPolynomial (Fin 3 × J) R) :
    (∑ v, expand 2 (p v) * monomial (blockExponent v) 1) = 0 ↔
      ∀ v, p v = 0 :=
  sum_expand_mul_monomial_eq_zero_iff blockExponent blockExponent_squarefree
    blockExponent_injective p

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_GenericPolynomial
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators
open scoped nonZeroDivisors

variable {σ : Type*}

theorem zmodTwo_sq (a : ZMod 2) : a ^ 2 = a := by
  classical
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl
  · exact zero_pow (by decide)
  · exact one_pow 2

theorem expand_two_eq_sq (p : MvPolynomial σ (ZMod 2)) : expand 2 p = p ^ 2 := by
  induction p using MvPolynomial.induction_on' with
  | monomial m a => simp only [expand_monomial, monomial_pow, zmodTwo_sq]
  | add p q hp hq => rw [map_add, CharTwo.add_sq, hp, hq]

theorem exists_coordinate_separator {X K : Type*} [Field K] [Fintype X]
    (W : Submodule K (X → K)) (v : X → K) (hv : v ∉ W) :
    ∃ a : X → K, (∀ w ∈ W, ∑ x, a x * w x = 0) ∧
      (∑ x, a x * v x) ≠ 0 := by
  classical
  obtain ⟨f, hfv, hfW⟩ := W.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let a : X → K := fun x => f (fun y => if x = y then 1 else 0)
  have hrepr (w : X → K) : f w = ∑ x, a x * w x := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  refine ⟨a, ?_, ?_⟩
  · intro w hw
    have hmem : f w ∈ W.map f := ⟨w, hw, rfl⟩
    rw [hfW, Submodule.mem_bot, hrepr] at hmem
    exact hmem
  · rwa [← hrepr]

variable {J X : Type*} [Fintype J] [Fintype X]

theorem universalLinearForm_prod (t : J → ZMod 2) :
    (∏ i, universalLinearForm t i) =
      ∑ v : Fin 3 → J, C (∏ i, t (v i)) * monomial (blockExponent v) 1 := by
  classical
  unfold universalLinearForm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.prod_mul_distrib, ← map_prod, monomial_blockExponent]

theorem alignmentObstruction_parity_expansion (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    alignmentObstruction t p = ∑ v : Fin 3 → J,
      cubicPairing t p v ^ 2 * monomial (blockExponent v) 1 := by
  classical
  unfold alignmentObstruction
  simp_rw [universalLinearForm_prod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  unfold cubicPairing
  rw [CharTwo.sum_sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  simp only [mul_pow, ← map_pow, zmodTwo_sq, mul_assoc]

theorem alignmentObstruction_ne_zero (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2))
    (v : Fin 3 → J) (hv : cubicPairing t p v ≠ 0) :
    alignmentObstruction t p ≠ 0 := by
  intro h
  rw [alignmentObstruction_parity_expansion] at h
  have hzero : ∀ w, cubicPairing t p w = 0 := by
    apply (sum_expand_mul_blockMonomial_eq_zero_iff _).mp
    simpa only [expand_two_eq_sq] using h
  exact hv (hzero v)

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

theorem eq_top_of_binary_coordinates
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hcoordinate : ∀ i, c i ∈ W)
    (hstable : ∀ i f, f ∈ W → (fun x => c i x * f x) ∈ W) :
    W = ⊤ := by
  classical
  have hindicator : ∀ x : X, (fun y => if x = y then (1 : F) else 0) ∈ W := by
    intro x
    have hfilter : ∀ s : Finset X,
        ∃ f : X → F, f ∈ W ∧ f x = 1 ∧ ∀ y ∈ s, y ≠ x → f y = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          obtain ⟨i, hi⟩ := hnonzero x
          refine ⟨c i, hcoordinate i, (hbinary i x).resolve_left hi, ?_⟩
          simp
      | @insert y s hy ih =>
          obtain ⟨f, hf, hfx, hfzero⟩ := ih
          by_cases hyx : y = x
          · refine ⟨f, hf, hfx, ?_⟩
            intro z hz hzx
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact (hzx hyx).elim
            · exact hfzero z hz hzx
          · obtain ⟨i, hi⟩ := hseparate x y (Ne.symm hyx)
            rcases hbinary i x with hix | hix <;>
              rcases hbinary i y with hiy | hiy
            · exact (hi (hix.trans hiy.symm)).elim
            · refine ⟨fun z => f z - c i z * f z,
                W.sub_mem hf (hstable i f hf), ?_, ?_⟩
              · simp [hfx, hix]
              · intro z hz hzx
                rcases Finset.mem_insert.mp hz with rfl | hz
                · simp [hiy]
                · simp [hfzero z hz hzx]
            · refine ⟨fun z => c i z * f z, hstable i f hf, ?_, ?_⟩
              · simp [hfx, hix]
              · intro z hz hzx
                rcases Finset.mem_insert.mp hz with rfl | hz
                · simp [hiy]
                · simp [hfzero z hz hzx]
            · exact (hi (hix.trans hiy.symm)).elim
    obtain ⟨f, hf, hfx, hfzero⟩ := hfilter Finset.univ
    have heq : f = fun y => if x = y then (1 : F) else 0 := by
      funext y
      by_cases hxy : x = y
      · subst y
        simp [hfx]
      · simp [hxy, hfzero y (Finset.mem_univ y) (Ne.symm hxy)]
    rwa [← heq]
  apply top_unique
  intro f _
  rw [pi_eq_sum_univ f]
  exact W.sum_mem fun x _ => W.smul_mem (f x) (hindicator x)

theorem eq_top_of_cubic_le_of_le_quadratic
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hcubic : cubicEvaluationSpan c ≤ W)
    (hquadratic : W ≤ quadraticEvaluationSpan c) : W = ⊤ := by
  apply eq_top_of_binary_coordinates c W hbinary hseparate hnonzero
  · intro i
    have hi : (fun x => c i x * c i x * c i x) ∈ cubicEvaluationSpan c :=
      Submodule.subset_span ⟨(i, i, i), rfl⟩
    have heq : (fun x => c i x * c i x * c i x) = c i := by
      funext x
      rcases hbinary i x with h | h <;> simp [h]
    rw [heq] at hi
    exact hcubic hi
  · intro k f hf
    have hf' : f ∈ Submodule.span F
        (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x) :=
      hquadratic hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hf
        have h : (fun x => c k x * c i x * c j x) ∈ cubicEvaluationSpan c :=
          Submodule.subset_span ⟨(k, i, j), rfl⟩
        simpa only [mul_assoc] using hcubic h
    | zero =>
        have heq : (fun x => c k x * (0 : X → F) x) = (0 : X → F) := by
          funext x
          exact mul_zero _
        rw [heq]
        exact W.zero_mem
    | add f g hf hg ihf ihg =>
        have heq : (fun x => c k x * ((f + g) x)) =
            (fun x => c k x * f x) + (fun x => c k x * g x) := by
          funext x
          exact mul_add _ _ _
        rw [heq]
        exact W.add_mem ihf ihg
    | smul a f hf ih =>
        have heq : (fun x => c k x * ((a • f) x)) =
            a • (fun x => c k x * f x) := by
          funext x
          exact mul_left_comm _ _ _
        rw [heq]
        exact W.smul_mem a ih

theorem binary_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

theorem exists_cubic_not_mem_of_finrank_lt
    {F X I : Type*} [Field F] [Fintype X]
    (c : I → X → F) (W : Submodule F (X → F))
    (hbinary : ∀ i x, c i x = 0 ∨ c i x = 1)
    (hseparate : ∀ x y, x ≠ y → ∃ i, c i x ≠ c i y)
    (hnonzero : ∀ x, ∃ i, c i x ≠ 0)
    (hquadratic : W ≤ quadraticEvaluationSpan c)
    (hdim : Module.finrank F W < Fintype.card X) :
    ∃ i j k, (fun x => c i x * c j x * c k x) ∉ W := by
  classical
  by_contra h
  have hcubic : cubicEvaluationSpan c ≤ W := by
    apply Submodule.span_le.mpr
    rintro f ⟨⟨i, j, k⟩, rfl⟩
    by_contra hn
    exact h ⟨i, j, k, hn⟩
  have htop := eq_top_of_cubic_le_of_le_quadratic c W hbinary hseparate
    hnonzero hcubic hquadratic
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
  exact (lt_irrefl _) hdim

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped nonZeroDivisors

theorem exists_polynomial_alignment_annihilator
    {J X : Type*} [Fintype J] [Fintype X]
    (t : X → J → ZMod 2) (ht : Function.Injective t)
    (hnonzero : ∀ x, t x ≠ 0) (hcard : 3 * Fintype.card J < Fintype.card X) :
    ∃ p : X → MvPolynomial (Fin 3 × J) (ZMod 2),
      (∀ ij, ∑ x, p x * universalAlignmentColumn t ij x = 0) ∧
      ∃ v : Fin 3 → J, cubicPairing t p v ≠ 0 := by
  classical
  let P := MvPolynomial (Fin 3 × J) (ZMod 2)
  let K := FractionRing P
  let f : P →+* K := algebraMap P K
  let φ : ZMod 2 →+* K := f.comp C
  let c : J → X → K := fun j x => φ (t x j)
  let M : Matrix X (Fin 3 × J) K := fun x ij => f (universalAlignmentColumn t ij x)
  let W := LinearMap.range M.mulVecLin
  have hquadratic : W ≤ quadraticEvaluationSpan c := by
    change LinearMap.range M.mulVecLin ≤ _
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    have heq : M.col ij = ∑ j, f (MvPolynomial.X (ij.1, j)) •
        (fun x => c ij.2 x * c j x) := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change f (C (t x ij.2) * ∑ j, C (t x j) * MvPolynomial.X (ij.1, j)) =
        ∑ j, f (MvPolynomial.X (ij.1, j)) * (f (C (t x ij.2)) * f (C (t x j)))
      simp only [map_mul, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ac_rfl
    rw [heq]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(ij.2, j), rfl⟩
  have hbinary : ∀ j x, c j x = 0 ∨ c j x = 1 := by
    intro j x
    rcases binary_eq_zero_or_one (t x j) with h | h
    · left
      simp [c, h]
    · right
      simp [c, h]
  have hseparate : ∀ x y, x ≠ y → ∃ j, c j x ≠ c j y := by
    intro x y hxy
    have hfun : t x ≠ t y := fun h => hxy (ht h)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hfun
    exact ⟨j, fun h => hj (φ.injective h)⟩
  have hnz : ∀ x, ∃ j, c j x ≠ 0 := by
    intro x
    obtain ⟨j, hj⟩ := Function.ne_iff.mp (hnonzero x)
    refine ⟨j, ?_⟩
    intro h
    exact hj (φ.injective (by simpa [c] using h))
  have hdim : Module.finrank K W < Fintype.card X := by
    have hle : Module.finrank K W ≤ 3 * Fintype.card J := by
      calc
        Module.finrank K W ≤ Module.finrank K ((Fin 3 × J) → K) :=
          LinearMap.finrank_range_le M.mulVecLin
        _ = 3 * Fintype.card J := by
          rw [Module.finrank_fintype_fun_eq_card]
          simp
    exact hle.trans_lt hcard
  obtain ⟨i, j, k, hijk⟩ := exists_cubic_not_mem_of_finrank_lt
    c W hbinary hseparate hnz hquadratic hdim
  let v : Fin 3 → J := ![i, j, k]
  have hcubic : (fun x => ∏ b : Fin 3, c (v b) x) ∉ W := by
    simpa [v, Fin.prod_univ_succ, mul_assoc] using hijk
  obtain ⟨a, ha, hav⟩ := exists_coordinate_separator W _ hcubic
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite P⁰ a
  choose p hp using hb
  have hp' (x : X) : f (p x) = f (b : P) * a x := by
    simpa only [Algebra.smul_def] using hp x
  have hbne : f (b : P) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  refine ⟨p, ?_, v, ?_⟩
  · intro ij
    apply IsFractionRing.injective P K
    change f (∑ x, p x * universalAlignmentColumn t ij x) = f 0
    rw [map_sum, map_zero]
    simp only [map_mul, hp', mul_assoc]
    rw [← Finset.mul_sum]
    have hcol : M.col ij ∈ W := by
      change M.col ij ∈ LinearMap.range M.mulVecLin
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨ij, rfl⟩
    have hsum := ha (M.col ij) hcol
    change (∑ x, a x * f (universalAlignmentColumn t ij x)) = 0 at hsum
    rw [hsum, mul_zero]
  · have heq : f (cubicPairing t p v) =
        f (b : P) * ∑ x, a x * ∏ i : Fin 3, c (v i) x := by
      unfold cubicPairing
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [hp', c, φ, map_prod, mul_assoc]
    intro hz
    have : f (b : P) * (∑ x, a x * ∏ i : Fin 3, c (v i) x) = 0 := by
      rw [← heq, hz, map_zero]
    exact (mul_ne_zero hbne hav) this

theorem alignmentObstruction_eval_eq_zero
    {J X F : Type*} [Fintype J] [Fintype X] [Field F] [CharP F 2]
    (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2))
    (hann : ∀ ij, ∑ x, p x * universalAlignmentColumn t ij x = 0)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F)
    (c : X → F) (a : (Fin 3 × J) → F)
    (hc : ∀ x, c x ^ 2 = ρ (∏ i, universalLinearForm (t x) i))
    (ha : ∀ x, c x = ∑ ij, ρ (universalAlignmentColumn t ij x) * a ij) :
    ρ (alignmentObstruction t p) = 0 := by
  classical
  have hann' (ij : Fin 3 × J) :
      (∑ x, ρ (p x) * ρ (universalAlignmentColumn t ij x)) = 0 := by
    have h := congrArg ρ (hann ij)
    simpa only [map_sum, map_mul, map_zero] using h
  have hpair : (∑ x, ρ (p x) * c x) = 0 := by
    simp_rw [ha, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro ij _
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, hann', zero_mul]
  calc
    ρ (alignmentObstruction t p) = ∑ x, ρ (p x) ^ 2 *
        ρ (∏ i, universalLinearForm (t x) i) := by
          simp only [alignmentObstruction, map_sum, map_mul, map_pow]
    _ = (∑ x, ρ (p x) * c x) ^ 2 := by
      rw [CharTwo.sum_sq]
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_pow, hc]
    _ = 0 := by rw [hpair, zero_pow (by decide)]

theorem exists_nonzero_alignment_obstruction
    {J X : Type*} [Fintype J] [Fintype X]
    (t : X → J → ZMod 2) (ht : Function.Injective t)
    (hnonzero : ∀ x, t x ≠ 0) (hcard : 3 * Fintype.card J < Fintype.card X) :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [CharP F 2]
        (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F)
        (c : X → F) (a : (Fin 3 × J) → F),
        (∀ x, c x ^ 2 = ρ (∏ i, universalLinearForm (t x) i)) →
        (∀ x, c x = ∑ ij, ρ (universalAlignmentColumn t ij x) * a ij) →
        ρ P = 0 := by
  obtain ⟨p, hann, v, hv⟩ := exists_polynomial_alignment_annihilator t ht hnonzero hcard
  refine ⟨alignmentObstruction t p, alignmentObstruction_ne_zero t p v hv, ?_⟩
  intro F _ _ ρ c a hc ha
  exact alignmentObstruction_eval_eq_zero t p hann ρ c a hc ha

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

omit [CharP F 2] in
theorem parameterMap_apply (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    parameterMap x t i = ∑ j, algebraMap (ZMod 2) F (t j) * x (i, j) := by
  classical
  simp [parameterMap, Basis.constr_apply_fintype, Algebra.smul_def]

omit [CharP F 2] in

theorem eval_universalLinearForm (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      parameterMap x t i := by
  rw [parameterMap_apply]
  simp [universalLinearForm]

omit [CharP F 2] in
theorem dot_parameter_lift (x : (Fin 3 × J) → F)
    (g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) (t : J → ZMod 2) :
    (∑ i, parameterMap x t i * g t i) =
      ∑ ij : Fin 3 × J,
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
          (universalAlignmentColumn (fun t : J → ZMod 2 => t) ij t) *
          g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1 := by
  have h := dot_lift_eq_alignment_mulVec (Pi.basisFun (ZMod 2) J)
    (fun t : J → ZMod 2 => t) (parameterMap x) g t
  simpa [Matrix.mulVec, dotProduct, alignmentMatrix, Pi.basisFun_repr,
    universalAlignmentColumn, eval_universalLinearForm] using h

variable [Fintype F]

theorem alignmentRightHandSide_sq (x : (Fin 3 × J) → F) (t : J → ZMod 2) :
    alignmentRightHandSide (parameterMap x t) ^ 2 =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
        (∏ i : Fin 3, universalLinearForm t i) := by
  simp [alignmentRightHandSide, Fin.prod_univ_succ, eval_universalLinearForm, mul_assoc]

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

theorem exists_all_lifts_alignment_polynomial (J : Type*) [Fintype J] [DecidableEq J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        ∀ g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F),
          (alignmentEvent (R := ZMod 2) (parameterMap x) g
            (fun t => alignmentRightHandSide (parameterMap x t))).card ≤
              3 * Fintype.card J := by
  classical
  let V := J → ZMod 2
  let Esets := {E : Finset V // (0 : V) ∉ E ∧ E.card = 3 * Fintype.card J + 1}
  have hex (E : Esets) := exists_nonzero_alignment_obstruction
    (fun t : E.val => (t : V)) Subtype.val_injective
    (fun t : E.val => by
      intro hz
      apply E.property.1
      simpa only [hz] using t.property)
    (show 3 * Fintype.card J < Fintype.card E.val by
      simpa only [Fintype.card_coe, E.property.2] using
        Nat.lt_succ_self (3 * Fintype.card J))
  choose p hp hvanish using hex
  let P : MvPolynomial (Fin 3 × J) (ZMod 2) := ∏ E : Esets, p E
  refine ⟨P, Finset.prod_ne_zero_iff.mpr (fun E _ => hp E), ?_⟩
  intro F _ _ _ _ x hP g
  by_contra hbad
  have hlarge : 3 * Fintype.card J + 1 ≤
      (alignmentEvent (R := ZMod 2) (parameterMap x) g
        (fun t => alignmentRightHandSide (parameterMap x t))).card := by omega
  obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hzero : (0 : V) ∉ E := by
    intro hz
    have hmem := hsub hz
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.1 rfl
  let E' : Esets := ⟨E, hzero, hcard⟩
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    MvPolynomial.eval₂Hom (algebraMap (ZMod 2) F) x
  let c : E → F := fun t => alignmentRightHandSide (parameterMap x (t : V))
  let a : (Fin 3 × J) → F :=
    fun ij => g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  have hc (t : E) :
      c t ^ 2 = ρ (∏ i : Fin 3, universalLinearForm (t : V) i) := by
    exact alignmentRightHandSide_sq x t
  have ha (t : E) : c t = ∑ ij, ρ
      (universalAlignmentColumn (fun t : E => (t : V)) ij t) * a ij := by
    have hmem := hsub t.property
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have ht := hmem.2
    calc
      c t = ∑ i, parameterMap x (t : V) i * g (t : V) i := ht.symm
      _ = _ := dot_parameter_lift x g t
  have hz : ρ (p E') = 0 := hvanish E' F ρ c a hc ha
  apply hP
  change ρ P = 0
  simp only [P, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ E') hz

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open MvPolynomial

theorem exists_binary_coordinate_one {J : Type*} (t : J → ZMod 2) (ht : t ≠ 0) :
    ∃ j, t j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ht
  exact ⟨j, (binary_eq_zero_or_one (t j)).resolve_left hj⟩

theorem exists_binary_minor_one {J : Type*} (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    ∃ j k, t j * u k + t k * u j = 1 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  by_cases huj : u j = 0
  · obtain ⟨k, hk⟩ := exists_binary_coordinate_one u hu
    exact ⟨j, k, by simp [hj, huj, hk]⟩
  · have huj' : u j = 1 := (binary_eq_zero_or_one (u j)).resolve_left huj
    obtain ⟨k, hk⟩ := Function.ne_iff.mp htu
    refine ⟨j, k, ?_⟩
    rcases binary_eq_zero_or_one (t k) with htk | htk <;>
      rcases binary_eq_zero_or_one (u k) with huk | huk
    · exact (hk (htk.trans huk.symm)).elim
    · simp [hj, huj', htk, huk]
    · simp [hj, huj', htk, huk]
    · exact (hk (htk.trans huk.symm)).elim

variable {J : Type*} [Fintype J]

theorem eval_universalLinearForm_selector_zero (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 0) = t j := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem eval_universalLinearForm_selector_one (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 1) = t k := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem universalLinearForm_zero_ne_zero (t : J → ZMod 2) (ht : t ≠ 0) :
    universalLinearForm t 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  intro h
  have hc := congrArg (eval (selectorAssignment j j)) h
  rw [eval_universalLinearForm_selector_zero, map_zero, hj] at hc
  exact one_ne_zero hc

theorem universalPairMinor_ne_zero (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    universalPairMinor t u ≠ 0 := by
  obtain ⟨j, k, hjk⟩ := exists_binary_minor_one t u ht hu htu
  intro h
  have hc := congrArg (eval (selectorAssignment j k)) h
  simp only [universalPairMinor, map_add, map_mul,
    eval_universalLinearForm_selector_zero, eval_universalLinearForm_selector_one,
    map_zero] at hc
  rw [hjk] at hc
  exact one_ne_zero hc

theorem universalPairMinor_eq_zero_of_proportional
    {F : Type*} [Field F] [CharP F 2]
    (t u : J → ZMod 2)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F) (a : F)
    (h : ∀ i, ρ (universalLinearForm t i) = a * ρ (universalLinearForm u i)) :
    ρ (universalPairMinor t u) = 0 := by
  simp only [universalPairMinor, map_add, map_mul, h]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (CharTwo.add_self_eq_zero
      (a * ρ (universalLinearForm u 0) * ρ (universalLinearForm u 1)))

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (J : Type*) [Fintype J]

theorem separationPolynomial_ne_zero : separationPolynomial J ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact universalLinearForm_zero_ne_zero t
      (Finset.mem_erase.mp ht).1
  · apply Finset.prod_ne_zero_iff.mpr
    intro tu htu
    have h := (Finset.mem_filter.mp htu).2
    exact universalPairMinor_ne_zero tu.1 tu.2 h.1 h.2.1 h.2.2

variable {J}

theorem parameterMap_separated_of_eval_ne_zero
    {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (x : (Fin 3 × J) → F)
    (hx : eval₂ (algebraMap (ZMod 2) F) x (separationPolynomial J) ≠ 0) :
    Function.Injective (parameterMap x) ∧
      ∀ t u : J → ZMod 2, t ≠ 0 → u ≠ 0 →
        (∃ a : F, parameterMap x t = a • parameterMap x u) → t = u := by
  classical
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    eval₂Hom (algebraMap (ZMod 2) F) x
  have hprod :
      (∏ t ∈ nonzeroBinaryInputs J, ρ (universalLinearForm t 0)) *
        (∏ tu ∈ distinctNonzeroBinaryPairs J, ρ (universalPairMinor tu.1 tu.2)) ≠ 0 := by
    change ρ (separationPolynomial J) ≠ 0 at hx
    simpa only [separationPolynomial, map_mul, map_prod] using hx
  have hlinear := (mul_ne_zero_iff.mp hprod).1
  have hminor := (mul_ne_zero_iff.mp hprod).2
  have hnonzero (t : J → ZMod 2) (ht : t ≠ 0) : parameterMap x t 0 ≠ 0 := by
    have hmem : t ∈ nonzeroBinaryInputs J := by
      simp [nonzeroBinaryInputs, ht]
    have h := Finset.prod_ne_zero_iff.mp hlinear t hmem
    change eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t 0) ≠ 0 at h
    rwa [eval_universalLinearForm] at h
  constructor
  · intro t u htu
    by_contra hne
    have hz : parameterMap x (t - u) = 0 := by
      rw [map_sub, htu, sub_self]
    exact hnonzero (t - u) (sub_ne_zero.mpr hne) (congrFun hz 0)
  · intro t u ht hu hprop
    by_contra hne
    have hmem : (t, u) ∈ distinctNonzeroBinaryPairs J := by
      simp [distinctNonzeroBinaryPairs, ht, hu, hne]
    have hnz := Finset.prod_ne_zero_iff.mp hminor (t, u) hmem
    obtain ⟨a, ha⟩ := hprop
    apply hnz
    apply universalPairMinor_eq_zero_of_proportional t u ρ a
    intro i
    change eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      a * eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm u i)
    rw [eval_universalLinearForm, eval_universalLinearForm]
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun ha i

end

end DFVSGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_PolynomialProbability
attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {F V : Type*} [Field F] [Fintype F] [CharP F 2]
variable [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem isGeneric_range_of_injective
    (z : V →ₗ[ZMod 2] (Fin 3 → F)) (hz : Function.Injective z)
    (hseparate : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      (∃ t : F, z v = t • z w) → v = w)
    (halign : ∀ g : V →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent z g (fun v => alignmentRightHandSide (z v))).card ≤
        3 * Module.finrank (ZMod 2) V) :
    IsGeneric (LinearMap.range z) := by
  classical
  let : Fintype (LinearMap.range z) := Subtype.fintype (Membership.mem (LinearMap.range z))
  let e : V ≃ₗ[ZMod 2] LinearMap.range z := LinearEquiv.ofInjective z hz
  have he (v : V) : ((e v : LinearMap.range z) : Fin 3 → F) = z v := rfl
  have hes (s : LinearMap.range z) : z (e.symm s) = (s : Fin 3 → F) :=
    LinearEquiv.ofInjective_symm_apply z s
  have hzero (v : V) : e v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h hv
      apply h
      rw [hv, map_zero]
    · intro h hv
      apply h
      apply e.injective
      simpa only [map_zero] using hv
  constructor
  · intro s t hs ht hprop
    have hs' : e.symm s ≠ 0 := by
      intro h
      apply hs
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have ht' : e.symm t ≠ 0 := by
      intro h
      apply ht
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have hinput : e.symm s = e.symm t := by
      apply hseparate _ _ hs' ht'
      simpa only [hes] using hprop
    exact e.symm.injective hinput
  · intro g
    have hevent (v : V) :
        v ∈ alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v)) ↔
        e v ∈ alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F)) := by
      simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        LinearMap.comp_apply, LinearEquiv.coe_coe, he, hzero]
    have hcard :
        (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card =
        (alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F))).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        exact (hevent v).mp hv
      · intro v hv w hw h
        exact e.injective h
      · intro s hs
        refine ⟨e.symm s, (hevent (e.symm s)).mpr ?_, e.apply_symm_apply s⟩
        simpa only [e.apply_symm_apply] using hs
    calc
      _ = (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card := hcard.symm
      _ ≤ 3 * Module.finrank (ZMod 2) V := halign _
      _ = 3 * Module.finrank (ZMod 2) (LinearMap.range z) :=
        congrArg (fun d : ℕ => 3 * d) e.finrank_eq

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Fintype F]

omit [Field F] in
theorem assignmentProbability_mono {n : ℕ}
    {event event' : (Fin n → F) → Prop} (h : ∀ x, event x → event' x) :
    assignmentProbability event ≤ assignmentProbability event' := by
  classical
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Finset.card_le_card
    (show Finset.univ.filter event ⊆ Finset.univ.filter event' from by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

theorem assignmentProbability_eval_zero_le {n : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  simpa [assignmentProbability] using
    MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)

omit [Fintype F] in

theorem totalDegree_map_eq_of_injective {σ : Type*}
    (φ : K →+* F) (hφ : Function.Injective φ) (p : MvPolynomial σ K) :
    (MvPolynomial.map φ p).totalDegree = p.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective p hφ]

theorem assignmentProbability_eval₂_zero_le {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval₂ φ x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  have hp' : MvPolynomial.map φ p ≠ 0 := by
    intro hz
    apply hp
    apply MvPolynomial.map_injective φ hφ
    simpa using hz
  have h := assignmentProbability_eval_zero_le (MvPolynomial.map φ p) hp'
  simpa only [← MvPolynomial.eval₂_eq_eval_map,
    totalDegree_map_eq_of_injective φ hφ] using h

theorem assignmentProbability_le_of_polynomial {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (event : (Fin n → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    assignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F :=
  (assignmentProbability_mono hvanish).trans
    (assignmentProbability_eval₂_zero_le φ hφ p hp)

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

omit [Field F] in
theorem finiteAssignmentProbability_reindex [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (event : (σ → F) → Prop) :
    finiteAssignmentProbability event =
      assignmentProbability (fun y : Fin n → F => event (fun s => y (e s))) := by
  classical
  have hcard : Fintype.card σ = n := by simpa using Fintype.card_congr e
  have hevent (x : σ → F) :
      event x ↔ event (fun s => reindexAssignments e x (e s)) := by
    simp [reindexAssignments]
  have hsub := Fintype.card_congr ((reindexAssignments (F := F) e).subtypeEquiv
    (p := event) (q := fun y : Fin n → F => event (fun s => y (e s))) hevent)
  have hfilter : (Finset.univ.filter event).card =
      (Finset.univ.filter (fun y : Fin n → F => event (fun s => y (e s)))).card := by
    simpa only [Fintype.card_subtype] using hsub
  simp only [finiteAssignmentProbability, assignmentProbability, hfilter, hcard]

theorem finiteAssignmentProbability_le_of_polynomial [Fintype σ]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial σ K) (hp : p ≠ 0)
    (event : (σ → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    finiteAssignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' := MvPolynomial.renameEquiv K e p
  have hp' : p' ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.renameEquiv K e).injective
    simpa only [map_zero] using h
  rw [finiteAssignmentProbability_reindex e event]
  have hbound := assignmentProbability_le_of_polynomial φ hφ p' hp'
    (fun y => event (fun s => y (e s))) (by
      intro y hy
      change MvPolynomial.eval₂ φ y (MvPolynomial.rename e p) = 0
      rw [MvPolynomial.eval₂_rename]
      exact hvanish (fun s => y (e s)) hy)
  simpa only [p', MvPolynomial.totalDegree_renameEquiv] using hbound

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

theorem exists_genericity_polynomial (J : Type*) [Fintype J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range := by
  classical
  obtain ⟨A, hA, halign⟩ := exists_all_lifts_alignment_polynomial J
  refine ⟨separationPolynomial J * A, mul_ne_zero (separationPolynomial_ne_zero J) hA, ?_⟩
  intro F _ _ _ _ x hP
  rw [MvPolynomial.eval₂_mul] at hP
  have hparts := mul_ne_zero_iff.mp hP
  have hsep := parameterMap_separated_of_eval_ne_zero x hparts.1
  refine ⟨hsep.1, isGeneric_range_of_injective (parameterMap x) hsep.1 hsep.2 ?_⟩
  intro g
  simpa only [Module.finrank_fintype_fun_eq_card] using halign F x hparts.2 g

theorem exists_genericity_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
          ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) ≤
            (D : ℚ≥0) / Fintype.card F := by
  classical
  obtain ⟨P, hP, hgood⟩ := exists_genericity_polynomial J
  refine ⟨P.totalDegree + 1, Nat.succ_pos _, ?_⟩
  intro F _ _ _ _
  have h := finiteAssignmentProbability_le_of_polynomial
    (algebraMap (ZMod 2) F) (algebraMap (ZMod 2) F).injective P hP
    (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range))
    (by
      intro x hx
      by_contra hne
      exact hx (hgood F x hne))
  apply h.trans
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Nat.le_succ P.totalDegree

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

omit [CharP F 2] in
theorem parameterMap_event_card
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    Nat.card {x : (Fin 3 × J) → F // event (parameterMap x)} =
      Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} := by
  exact Nat.card_congr ((parameterMapEquiv (F := F) (J := J)).subtypeEquiv
    (p := fun x => event (parameterMap x)) (q := event) (fun _ => Iff.rfl))

variable [Fintype F]

omit [CharP F 2] in
theorem parameterMap_event_probability
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    (finiteAssignmentProbability (fun x => event (parameterMap x)) : ℚ) =
      (Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} : ℚ) /
        Nat.card ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) := by
  classical
  have hall := Nat.card_congr (parameterMapEquiv (F := F) (J := J))
  have hevent := parameterMap_event_card event
  rw [← hevent, ← hall]
  simp [finiteAssignmentProbability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ] ; congr 1 ; ext x ; simp

end

end DFVSGames.Quadratic

noncomputable section

open scoped BigOperators
open Module
open DFVSGames.Gadget.Orientation

namespace DFVSGames.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

omit [FiniteDimensional K W] in

theorem injection_transitive (J₁ J₂ : Injection K V W) :
    ∃ a : W ≃ₗ[K] W, a • J₁ = J₂ := by
  let e₁ := LinearEquiv.ofInjective J₁.val J₁.property
  let e₂ := LinearEquiv.ofInjective J₂.val J₂.property
  let e : LinearMap.range J₁.val ≃ₗ[K] LinearMap.range J₂.val := e₁.symm.trans e₂
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext x
  have h := (ha (e₁ x)).symm
  change a (J₁.val x) = ((e₂ (e₁.symm (e₁ x))) : W) at h
  change a (J₁.val x) = J₂.val x
  simpa only [LinearEquiv.symm_apply_apply, e₂, LinearEquiv.ofInjective_apply] using h

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem image_action (a : W ≃ₗ[K] W) (J : Injection K V W) :
    image (a • J) = a • image J := by
  apply Subtype.ext
  exact LinearMap.range_comp J.val a.toLinearMap

variable [Fintype (W ≃ₗ[K] W)] [Fintype (Injection K V W)]
    [Fintype (RankSpace K W (finrank K V))]

theorem mean_image (J₀ : Injection K V W) (f : RankSpace K W (finrank K V) → ℚ) :
    (∑ J : Injection K V W, f (image J)) / Fintype.card (Injection K V W) =
      (∑ S : RankSpace K W (finrank K V), f S) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  have h := mean_action J₀ (injection_transitive J₀) (fun J => f (image J))
  simp_rw [image_action] at h
  exact h.symm.trans (mean_oriented_subspace (image J₀) f)

theorem bad_image_count_ratio (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) :
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) /
        Fintype.card (Injection K V W) =
      (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  classical
  have h := mean_image J₀ (fun S => if Bad S then 1 else 0)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem bad_subspace_bound (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) (α β : ℚ) (hα : 0 ≤ α) (hβ : β < 1)
    (hbad : (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) ≤
      α * Nat.card (V →ₗ[K] W))
    (hinj : (1 - β) * Nat.card (V →ₗ[K] W) ≤ Fintype.card (Injection K V W)) :
    (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) ≤ α / (1 - β) := by
  rw [← bad_image_count_ratio J₀ Bad]
  have : Nonempty (Injection K V W) := ⟨J₀⟩
  have hi : (0 : ℚ) < Fintype.card (Injection K V W) := by
    exact_mod_cast Fintype.card_pos
  have hd : 0 < 1 - β := sub_pos.mpr hβ
  apply (div_le_div_iff₀ hi hd).mpr
  calc
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) * (1 - β) ≤
        (α * Nat.card (V →ₗ[K] W)) * (1 - β) :=
      mul_le_mul_of_nonneg_right hbad hd.le
    _ = α * ((1 - β) * Nat.card (V →ₗ[K] W)) := by ring
    _ ≤ α * Fintype.card (Injection K V W) := mul_le_mul_of_nonneg_left hinj hα

end DFVSGames.Quadratic.UniformSubspaces
end

noncomputable section

open Module
open DFVSGames.Gadget.Orientation

namespace DFVSGames.Quadratic

private theorem conditioning_counts_inline_GenericSubspaceProbability {A : Type*} [Fintype A] [Nonempty A]
    (P Q : A → Prop) (α : ℚ) (hα : α < 1)
    (hbad : (Nat.card {a : A // ¬(P a ∧ Q a)} : ℚ) / Nat.card A ≤ α) :
    (∃ a : A, P a ∧ Q a) ∧
      (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤ α * Nat.card A ∧
      (1 - α) * Nat.card A ≤ (Nat.card {a : A // P a} : ℚ) := by
  classical
  have hpos : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hbadCount := (div_le_iff₀ hpos).mp hbad
  have hgood : ∃ a : A, P a ∧ Q a := by
    by_contra h
    have hall : ∀ a : A, ¬(P a ∧ Q a) := fun a ha => h ⟨a, ha⟩
    have hcard : Nat.card {a : A // ¬(P a ∧ Q a)} = Nat.card A := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hall]
    rw [hcard, div_self hpos.ne'] at hbad
    exact (not_le_of_gt hα) hbad
  have hnoninj : Nat.card {a : A // ¬P a} ≤ Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : A // ¬P a} => (⟨a.1, fun h => a.2 h.1⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hbadInj : Nat.card {a : {a : A // P a} // ¬Q a.1} ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : {a : A // P a} // ¬Q a.1} =>
        (⟨a.1.1, fun h => a.2 h.2⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hpartitionNat : Nat.card {a : A // P a} + Nat.card {a : A // ¬P a} = Nat.card A := by
    have hle := Fintype.card_subtype_le P
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    omega
  have hpartition : (Nat.card {a : A // P a} : ℚ) +
      Nat.card {a : A // ¬P a} = Nat.card A := by exact_mod_cast hpartitionNat
  have hn : (Nat.card {a : A // ¬P a} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hnoninj
  have hb : (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hbadInj
  refine ⟨hgood, hb.trans hbadCount, ?_⟩
  linarith

variable {F J : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] [Fintype J]

theorem generic_subspace_and_probability_of_parameter_error (α : ℚ)
    (hα₀ : 0 ≤ α) (hα : α < 1)
    (herror : (finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) : ℚ) ≤ α) :
    (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
      nongenericFraction F (Fintype.card J) ≤ α / (1 - α) := by
  classical
  let V := J → ZMod 2
  let W := Fin 3 → F
  let A := V →ₗ[ZMod 2] W
  let P : A → Prop := fun g => Function.Injective g
  let Q : A → Prop := fun g => IsGeneric g.range
  let : Fintype A := Fintype.ofEquiv ((Fin 3 × J) → F) parameterMapEquiv
  let : Fintype (Submodule (ZMod 2) W) :=
    Fintype.ofInjective (fun S : Submodule (ZMod 2) W => (S : Set W)) SetLike.coe_injective
  let : Fintype (W ≃ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  let : Fintype (UniformSubspaces.Injection (ZMod 2) V W) :=
    inferInstanceAs (Fintype {g : A // Function.Injective g})
  let : Fintype (RankSpace (ZMod 2) W (finrank (ZMod 2) V)) :=
    inferInstanceAs (Fintype {S : Submodule (ZMod 2) W // finrank (ZMod 2) S = finrank (ZMod 2) V})
  have hcount : (Nat.card {g : A // ¬(P g ∧ Q g)} : ℚ) / Nat.card A ≤ α := by
    rw [parameterMap_event_probability (fun g : A => ¬(P g ∧ Q g))] at herror
    exact herror
  have hc := conditioning_counts_inline_GenericSubspaceProbability P Q α hα hcount
  obtain ⟨g, hgP, hgQ⟩ := hc.1
  let J₀ : UniformSubspaces.Injection (ZMod 2) V W := ⟨g, hgP⟩
  have hdim : finrank (ZMod 2) V = Fintype.card J :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hfrac := UniformSubspaces.bad_subspace_bound J₀
    (fun S : RankSpace (ZMod 2) W (finrank (ZMod 2) V) => ¬IsGeneric S.1)
    α α hα₀ hα hc.2.1 (by
      rw [← Nat.card_eq_fintype_card]
      exact hc.2.2)
  refine ⟨?_, ?_⟩
  · refine ⟨⟨g.range, ?_⟩, hgQ⟩
    simpa only [V, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_of_inj hgP)
  · rw [← Nat.card_eq_fintype_card] at hfrac
    change nongenericFraction F (finrank (ZMod 2) V) ≤ α / (1 - α) at hfrac
    simpa only [hdim] using hfrac

theorem exists_generic_subspace_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        (D : ℚ) / Fintype.card F < 1 →
        (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
          nongenericFraction F (Fintype.card J) ≤
            ((D : ℚ) / Fintype.card F) / (1 - (D : ℚ) / Fintype.card F) := by
  obtain ⟨D, hD, hbound⟩ := exists_genericity_error_numerator J
  refine ⟨D, hD, ?_⟩
  intro F _ _ _ _ hsmall
  apply generic_subspace_and_probability_of_parameter_error ((D : ℚ) / Fintype.card F)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsmall
  exact_mod_cast hbound F

theorem conditional_error_le_of_small (α ε : ℚ) (hα : 0 ≤ α)
    (hhalf : α ≤ 1 / 2) (hε : α ≤ ε / 2) : α / (1 - α) ≤ ε := by
  have hd : 0 < 1 - α := by linarith
  apply (div_le_iff₀ hd).mpr
  have hε₀ : 0 ≤ ε := by linarith
  have hprod : 0 ≤ ε * (1 / 2 - α) := mul_nonneg hε₀ (by linarith)
  nlinarith

end DFVSGames.Quadratic
end

namespace DFVSGames.Quadratic

theorem card_binaryField (d : ℕ) (hd : 0 < d) :
    Nat.card (BinaryField d) = 2 ^ d :=
  GaloisField.card 2 d (Nat.ne_of_gt hd)

theorem finrank_binaryField (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (BinaryField d) = d :=
  GaloisField.finrank 2 (Nat.ne_of_gt hd)

theorem finrank_binaryField_triple (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (Fin 3 → BinaryField d) = 3 * d := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (BinaryField d) (Fin 3 → BinaryField d),
    finrank_binaryField d hd, Module.finrank_fin_fun, mul_comm]

theorem fieldDegree_pos (N r : ℕ) : 0 < fieldDegree N r := by
  simp [fieldDegree]

theorem threshold_lt_two_pow_fieldDegree (N r : ℕ) : N < 2 ^ fieldDegree N r := by
  have h : N ≤ fieldDegree N r := by unfold fieldDegree; omega
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

theorem rankThreshold_le_triple_fieldDegree (N r : ℕ) : r ≤ 3 * fieldDegree N r := by
  unfold fieldDegree
  omega

theorem chosen_binaryField_thresholds (N r : ℕ) :
    N < Nat.card (BinaryField (fieldDegree N r)) ∧
      r ≤ Module.finrank (ZMod 2) (Fin 3 → BinaryField (fieldDegree N r)) := by
  rw [card_binaryField _ (fieldDegree_pos N r),
    finrank_binaryField_triple _ (fieldDegree_pos N r)]
  exact ⟨threshold_lt_two_pow_fieldDegree N r, rankThreshold_le_triple_fieldDegree N r⟩

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators
open DFVSGames.Gadget.Orientation

noncomputable section

theorem exists_uniform_generic_field (r₀ : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ r₀ ≤ 3 * d ∧
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction (BinaryField d) r ≤ ε) ∧
      (∃ S : RankSpace (ZMod 2) (Fin 3 → BinaryField d) r₀, IsGeneric S.1) := by
  classical
  have hex (r : ℕ) := exists_generic_subspace_error_numerator (Fin r)
  choose D hD hbound using hex
  let M : ℕ := ∑ r ∈ Finset.range (r₀ + 1), D r
  have hDM (r : ℕ) (hr : r ≤ r₀) : D r ≤ M := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (M : ℚ)) (2 * (M : ℚ) / ε))
  let d := fieldDegree N r₀
  have hd : 0 < d := fieldDegree_pos N r₀
  have hqN : (N : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card] using
        (chosen_binaryField_thresholds N r₀).1)
  have hq : (0 : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast Fintype.card_pos
  have hqM : 2 * (M : ℚ) < Fintype.card (BinaryField d) :=
    (le_max_left _ _).trans_lt (hN.trans hqN)
  have hqε : 2 * (M : ℚ) / ε < Fintype.card (BinaryField d) :=
    (le_max_right _ _).trans_lt (hN.trans hqN)
  have hεq : 2 * (M : ℚ) < (Fintype.card (BinaryField d) : ℚ) * ε :=
    (div_lt_iff₀ hε).mp hqε
  have hsmall (r : ℕ) (hr : r ≤ r₀) :
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ 1 / 2 ∧
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ ε / 2 := by
    have hDr : (D r : ℚ) ≤ M := by exact_mod_cast hDM r hr
    constructor
    · apply (div_le_iff₀ hq).mpr
      nlinarith
    · apply (div_le_iff₀ hq).mpr
      nlinarith
  have hready (r : ℕ) (hr : r ≤ r₀) :=
    hbound r (BinaryField d) (show (D r : ℚ) / Fintype.card (BinaryField d) < 1 by
      have := (hsmall r hr).1
      linarith)
  refine ⟨d, hd, rankThreshold_le_triple_fieldDegree N r₀, ?_, ?_⟩
  · intro r hr
    have hb := (hready r hr).2
    simp only [Fintype.card_fin] at hb
    apply hb.trans
    exact conditional_error_le_of_small _ _
      (div_nonneg (Nat.cast_nonneg _) hq.le) (hsmall r hr).1 (hsmall r hr).2
  · obtain ⟨S, hS⟩ := (hready r₀ le_rfl).1
    refine ⟨⟨S.1, ?_⟩, hS⟩
    simpa only [Fintype.card_fin] using S.2

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

attribute [local instance] OAI.DFVSGames.Gadget.BaseConstruction.indexDecidableEq
local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem theta_le_one : fieldLineTheta F ≤ 1 := by
  have hc : (1 : ℚ) ≤ Nat.card (FieldLine F) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (card_FieldLine_pos (F := F)))
  exact (inv_anti₀ (by norm_num : (0 : ℚ) < 1) hc).trans_eq (by norm_num)

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem rate_eq_one_sub_theta : rate F = 1 - fieldLineTheta F := by
  rw [rate, fieldLineTheta_eq, one_div]

theorem quotient_detection
    (r₀ : ℕ) (ε : ℚ) (hr₀ : 0 < r₀)
    (hbudget : badRankCoefficient r₀ * ε ≤ 1)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
    (S₀ : Submodule (ZMod 2) (Vec F))
    (hrank : Module.finrank (ZMod 2) S₀ = r₀) (hS₀ : IsGeneric S₀)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (T : (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).Input →ₗ[ZMod 2] E)
    (hinj : Function.Injective
      (T.comp (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).embed)) :
    (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
      if T ((quotientStage (F := F) (depth r₀ (fieldLineTheta F))).noise t) ≠ 0
      then 1 else 0) := by
  classical
  let n := depth r₀ (fieldLineTheta F)
  let : Fintype (stage (F := F) n).Noise := DescentProbability.noiseFintype
    (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n
  have hJ : Function.Surjective
      (aggregate (OrientedBlockKernel.orientedBlockLinear (F := F))) := by
    exact aggregate_blockEmbedding_surjective (F := F)
  have hfull : ∀ L : Lift (stage (F := F) n)
      (⊤ : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Vec F))),
      (1 / 4 : ℚ) ≤ probability (fun t => ∃ z, L.family z ((stage n).noise t) ≠ 0) := by
    intro L
    exact BaseDetection.full_lift_detection hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  have h := QuotientDetection.target_detection_after_quotient
    (stage (F := F) n) T (1 / 4) hfull hinj
  change (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average
    (fun t : (stage (F := F) n).Noise =>
      if T (StageQuotient.noise (stage (F := F) n) t) ≠ 0 then 1 else 0)
  rw [StageNoiseRecurrence.average_eq_expect]
  exact h

theorem quotient_error_le (p : ℚ) (r₀ : ℕ)
    (hgeom : (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) ≤ p) :
    StageNoiseRecurrence.error
      (quotientStage (F := F) (depth r₀ (fieldLineTheta F))) ≤ p := by
  rw [quotientStage_error, rate_eq_one_sub_theta]
  have hpow : 0 ≤ (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) :=
    pow_nonneg (sub_nonneg.mpr theta_le_one) _
  have hcoef : 1 - 1 / (Nat.card F : ℚ) ^ 3 ≤ 1 :=
    sub_le_self _ (by positivity)
  exact (mul_le_of_le_one_left hpow hcoef).trans hgeom

theorem exists_base_oai (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  obtain ⟨r₀, ε, hr₀, hε, _hεone, hbudget, hgeom⟩ := effective_parameters p hp
  obtain ⟨d, hd, _hdim, hgeneric, S₀, hS₀⟩ :=
    exists_uniform_generic_field r₀ ε hε
  refine ⟨d, hd, depth r₀ (fieldLineTheta (BinaryField d)), ?_, ?_⟩
  · exact quotient_error_le p r₀
      (hgeom _ BaseDetection.theta_pos theta_le_one)
  · intro E _ _ T hinj
    exact quotient_detection r₀ ε hr₀ hbudget hgeneric S₀.1 S₀.2 hS₀ T hinj

end

end DFVSGames.Gadget.BaseConstruction

end OAI
end

theorem solution : type_of% @OAI.DFVSGames.Gadget.BaseConstruction.exists_base_oai := @OAI.DFVSGames.Gadget.BaseConstruction.exists_base_oai
