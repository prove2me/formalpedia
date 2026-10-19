-- Prove2me | solution 1 for OAI.UniversalCoverSplitting.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:59:22.585414+00:00
-- url     : https://prove2.me/submissions/aa9e9fe2-0d41-490c-8f7d-587a986af991

import Mathlib
import Definitions.Def_KahlerSplitting
import Definitions.Def_OAIQWUCS004

section
-- module Solutions.OAIQW_UniversalCover.Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace RectangleGrid
variable {P Q X : Type*}

theorem row (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (a : ℕ → P → X) (ha : ∀ i, a i ∈ H) (lo hi : ℕ → P)
    (join : ∀ i, a i (hi i)=a (i+1) (lo (i+1)))
    (b : Q → X) (hb : b ∈ V) (q : Q) (corner : a 0 (lo 0)=b q) :
    ∃ f : ℕ → P × Q → X, (∀ i, f i ∈ T) ∧
      (∀ i x, f i (x,q)=a i x) ∧ (∀ y, f 0 (lo 0,y)=b y) ∧
      (∀ i y, f i (hi i,y)=f (i+1) (lo (i+1),y)) := by
  classical
  let State (i : ℕ) := {c : Q → X // c ∈ V ∧ a i (lo i)=c q}
  have exist (i : ℕ) (c : State i) := fill (a i) (ha i) c.val c.property.1 (lo i) q c.property.2
  let tile (i : ℕ) (c : State i) : P × Q → X := (exist i c).choose
  have tileT (i : ℕ) (c : State i) : tile i c ∈ T := (exist i c).choose_spec.1
  have bottom (i : ℕ) (c : State i) (x : P) : tile i c (x,q)=a i x :=
    (exist i c).choose_spec.2.1 x
  have left (i : ℕ) (c : State i) (y : Q) : tile i c (lo i,y)=c.val y :=
    (exist i c).choose_spec.2.2 y
  let next (i : ℕ) (c : State i) : State (i+1) :=
    ⟨fun y ↦ tile i c (hi i,y),vertical _ (tileT i c) _,((bottom i c (hi i)).trans (join i)).symm⟩
  let seq : (i : ℕ) → State i := Nat.rec ⟨b,hb,corner⟩ next
  refine ⟨fun i ↦ tile i (seq i),fun i ↦ tileT i _,fun i x ↦ bottom i _ x,left 0 _,?_⟩
  intro i y
  exact (left (i+1) (seq (i+1)) y).symm

theorem grid (H : Set (P → X)) (V : Set (Q → X)) (T : Set (P × Q → X))
    (horizontal : ∀ f ∈ T, ∀ q, (fun p ↦ f (p,q)) ∈ H)
    (vertical : ∀ f ∈ T, ∀ p, (fun q ↦ f (p,q)) ∈ V)
    (fill : ∀ a ∈ H, ∀ b ∈ V, ∀ p q, a p=b q →
      ∃ f ∈ T, (∀ x, f (x,q)=a x) ∧ (∀ y, f (p,y)=b y))
    (a : ℕ → P → X) (ha : ∀ i, a i ∈ H) (lo hi : ℕ → P)
    (joinA : ∀ i, a i (hi i)=a (i+1) (lo (i+1)))
    (b : ℕ → Q → X) (hb : ∀ j, b j ∈ V) (bot top : ℕ → Q)
    (joinB : ∀ j, b j (top j)=b (j+1) (bot (j+1)))
    (corner : a 0 (lo 0)=b 0 (bot 0)) :
    ∃ f : ℕ → ℕ → P × Q → X, (∀ i j, f i j ∈ T) ∧
      (∀ i x, f i 0 (x,bot 0)=a i x) ∧
      (∀ j y, f 0 j (lo 0,y)=b j y) ∧
      (∀ i j y, f i j (hi i,y)=f (i+1) j (lo (i+1),y)) ∧
      (∀ i j x, f i j (x,top j)=f i (j+1) (x,bot (j+1))) := by
  classical
  let State (j : ℕ) := {c : ℕ → P → X //
    (∀ i, c i ∈ H) ∧ (∀ i, c i (hi i)=c (i+1) (lo (i+1))) ∧ c 0 (lo 0)=b j (bot j)}
  have exist (j : ℕ) (c : State j) :=
    row H V T vertical fill c.val c.property.1 lo hi c.property.2.1
      (b j) (hb j) (bot j) c.property.2.2
  let tiles (j : ℕ) (c : State j) := (exist j c).choose
  have ht (j : ℕ) (c : State j) (i : ℕ) : tiles j c i ∈ T := (exist j c).choose_spec.1 i
  have bottom (j : ℕ) (c : State j) (i : ℕ) (x : P) :
      tiles j c i (x,bot j)=c.val i x := (exist j c).choose_spec.2.1 i x
  have left (j : ℕ) (c : State j) (y : Q) :
      tiles j c 0 (lo 0,y)=b j y := (exist j c).choose_spec.2.2.1 y
  have seam (j : ℕ) (c : State j) (i : ℕ) (y : Q) :
      tiles j c i (hi i,y)=tiles j c (i+1) (lo (i+1),y) :=
    (exist j c).choose_spec.2.2.2 i y
  let next (j : ℕ) (c : State j) : State (j+1) :=
    ⟨fun i x ↦ tiles j c i (x,top j),fun i ↦ horizontal _ (ht j c i) _,
      fun i ↦ seam j c i _,(left j c (top j)).trans (joinB j)⟩
  let seq : (j : ℕ) → State j := Nat.rec ⟨a,ha,joinA,corner⟩ next
  refine ⟨fun i j ↦ tiles j (seq j) i,fun i j ↦ ht j _ i,
    bottom 0 _,fun j y ↦ left j _ y,fun i j y ↦ seam j _ i y,?_⟩
  intro i j x
  exact (bottom (j+1) (seq (j+1)) i x).symm

end RectangleGrid
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.CommutingFlows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Metric Filter Topology
open scoped ContDiff

open Set Filter Topology Metric Complex
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

variable [CompleteSpace F]

theorem finite_holomorphic_contDiffOn_one [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from by simp, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hf,by simp,?_⟩
  rw [contDiffOn_zero]
  intro p hp
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_clm_apply]
  exact continuousAt_directional_fderiv hU hf hp

end UniversalCoverSplitting

open Set Metric Filter Topology

open Set Metric Filter Topology

open Set Metric Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PolydiskAxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s d e : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem holomorphic_grid [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (a : ℕ → Polydisk d → X.Carrier) (ha : ∀ i, IsDiskHorizontal S (a i))
    (lo hi : ℕ → Polydisk d) (joinA : ∀ i, a i (hi i)=a (i+1) (lo (i+1)))
    (b : ℕ → Polydisk e → X.Carrier) (hb : ∀ j, IsDiskVertical S (b j))
    (bot top : ℕ → Polydisk e) (joinB : ∀ j, b j (top j)=b (j+1) (bot (j+1)))
    (corner : a 0 (lo 0)=b 0 (bot 0)) :
    ∃ f : ℕ → ℕ → Polydisk d × Polydisk e → X.Carrier,
      (∀ i j, IsDiskTile S (f i j)) ∧
      (∀ i x, f i 0 (x,bot 0)=a i x) ∧ (∀ j y, f 0 j (lo 0,y)=b j y) ∧
      (∀ i j y, f i j (hi i,y)=f (i+1) j (lo (i+1),y)) ∧
      (∀ i j x, f i j (x,top j)=f i (j+1) (x,bot (j+1))) := by
  exact RectangleGrid.grid {a | IsDiskHorizontal S a} {b | IsDiskVertical S b}
    {f | IsDiskTile S f} (fun _ h q ↦ h.horizontal q) (fun _ h p ↦ h.vertical p)
    (fun _ hA _ hB p q hc ↦ disk_fill g h₁ h₂ hA hB p q hc)
    a ha lo hi joinA b hb bot top joinB corner

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PathBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {A B X C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma IsVertical.precomp {atlas : Set (OpenPartialHomeomorph X (C × D))}
    {f : A → X} (hf : IsVertical atlas f) {a : B → A} (ha : Continuous a) :
    IsVertical atlas (f ∘ a) := by
  refine ⟨hf.1.comp ha,fun e he ↦ ?_⟩
  exact (hf.2 e he).comp_continuous
    ((ha.comp continuous_subtype_val).subtype_mk fun x ↦ x.property)

end ProductBoxTopology

open Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A]

lemma horizontal_local_parameter (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {α : A → X.Carrier}
    (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) α) (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ f : Polydisk r → X.Carrier,
      IsDiskHorizontal S f ∧ ∃ a : U → Polydisk r, Continuous a ∧ ∀ y, f (a y)=α y := by
  obtain ⟨e,hxe,he0⟩ := exists_splittingChart S h₁ h₂ (α x)
  let W := α ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hα.1
  have hlc := (hα.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨x,hxe⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨x,hxe⟩ _).mp hlc
  obtain ⟨U,hUV,hU,hxU⟩ := mem_nhds_iff.mp (inter_mem hV (hW.mem_nhds hxe))
  have heU (y : U) : α y ∈ e.chart.source := (hUV y.property).2
  have hcoord (y : U) : (e.chart (α y)).2=0 := by
    have hh := hsub (show (⟨y,heU y⟩ : W) ∈ Subtype.val ⁻¹' V from (hUV y.property).1)
    change (e.chart (α y)).2=(e.chart (α x)).2 at hh
    rw [he0] at hh
    exact hh
  let a : U → Polydisk r := fun y ↦ ⟨(e.radius : ℂ)⁻¹ • (e.chart (α y)).1,
    unscale_mem_ball e.radius_pos (by
      have hh := e.chart.map_source (heU y)
      rw [e.product_range] at hh
      exact hh.1)⟩
  have ha : Continuous a := by
    apply Continuous.subtype_mk
    exact ((e.chart.continuousOn.comp_continuous (hα.1.comp continuous_subtype_val)
      heU).fst.const_smul ((e.radius : ℂ)⁻¹))
  let q : Polydisk s := ⟨0,mem_ball_self zero_lt_one⟩
  refine ⟨U,hU,hxU,fun p ↦ e.unitMap (p,q),
    ⟨fun p ↦ e.unitMap (p,0),e.unitMap_block.horizontal_slice isOpen_ball isOpen_ball q.property,
      fun _ ↦ rfl⟩,a,ha,?_⟩
  intro y
  have hh := e.unitMap_coordinates (heU y)
  simpa only [hcoord y,smul_zero] using hh

lemma vertical_local_parameter (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {β : A → X.Carrier}
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β) (x : A) :
    ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ f : Polydisk s → X.Carrier,
      IsDiskVertical S f ∧ ∃ b : U → Polydisk s, Continuous b ∧ ∀ y, f (b y)=β y := by
  obtain ⟨e,hxe,he0⟩ := exists_splittingChart S h₁ h₂ (β x)
  let W := β ⁻¹' e.chart.source
  have hW : IsOpen W := e.chart.open_source.preimage hβ.1
  have hlc := (hβ.2 e.chart ⟨e,rfl⟩).eventually_eq (⟨x,hxe⟩ : W)
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨x,hxe⟩ _).mp hlc
  obtain ⟨U,hUV,hU,hxU⟩ := mem_nhds_iff.mp (inter_mem hV (hW.mem_nhds hxe))
  have heU (y : U) : β y ∈ e.chart.source := (hUV y.property).2
  have hcoord (y : U) : (e.chart (β y)).1=0 := by
    have hh := hsub (show (⟨y,heU y⟩ : W) ∈ Subtype.val ⁻¹' V from (hUV y.property).1)
    change (e.chart (β y)).1=(e.chart (β x)).1 at hh
    rw [he0] at hh
    exact hh
  let b : U → Polydisk s := fun y ↦ ⟨(e.radius : ℂ)⁻¹ • (e.chart (β y)).2,
    unscale_mem_ball e.radius_pos (by
      have hh := e.chart.map_source (heU y)
      rw [e.product_range] at hh
      exact hh.2)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact ((e.chart.continuousOn.comp_continuous (hβ.1.comp continuous_subtype_val)
      heU).snd.const_smul ((e.radius : ℂ)⁻¹))
  let p : Polydisk r := ⟨0,mem_ball_self zero_lt_one⟩
  refine ⟨U,hU,hxU,fun q ↦ e.unitMap (p,q),
    ⟨fun q ↦ e.unitMap (0,q),e.unitMap_block.vertical_slice isOpen_ball isOpen_ball p.property,
      fun _ ↦ rfl⟩,b,hb,?_⟩
  intro y
  have hh := e.unitMap_coordinates (heU y)
  simpa only [hcoord y,smul_zero] using hh

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
open IntervalChain
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem path_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α β : I → X.Carrier} (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) α)
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β) (hbase : α 0=β 0) :
    ∃ R : I × I → X.Carrier, ProductBoxTopology.IsBox (splittingAtlas S) R ∧
      (∀ x, R (x,0)=α x) ∧ (∀ y, R (0,y)=β y) := by
  obtain ⟨t,ht0,ht,⟨N,hN⟩,A,hA,a,ha,eA⟩ :=
    PathSubdivision.parameterize α (IsDiskHorizontal S) (horizontal_local_parameter h₁ h₂ hα)
  obtain ⟨u,hu0,hu,⟨M,hM⟩,B,hB,b,hb,eB⟩ :=
    PathSubdivision.parameterize β (IsDiskVertical S) (vertical_local_parameter h₁ h₂ hβ)
  let lo : ℕ → Polydisk r := fun i ↦ a i ⟨t i,le_rfl,ht (Nat.le_succ i)⟩
  let hi : ℕ → Polydisk r := fun i ↦ a i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩
  let bot : ℕ → Polydisk s := fun j ↦ b j ⟨u j,le_rfl,hu (Nat.le_succ j)⟩
  let top : ℕ → Polydisk s := fun j ↦ b j ⟨u (j+1),hu (Nat.le_succ j),le_rfl⟩
  have joinA (i : ℕ) : A i (hi i)=A (i+1) (lo (i+1)) :=
    (eA i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩).trans
      (eA (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩).symm
  have joinB (j : ℕ) : B j (top j)=B (j+1) (bot (j+1)) :=
    (eB j ⟨u (j+1),hu (Nat.le_succ j),le_rfl⟩).trans
      (eB (j+1) ⟨u (j+1),le_rfl,hu (Nat.le_succ (j+1))⟩).symm
  have corner : A 0 (lo 0)=B 0 (bot 0) := by
    change A 0 (a 0 _)=B 0 (b 0 _)
    rw [eA,eB]
    change α (t 0)=β (u 0)
    simpa only [ht0,hu0] using hbase
  obtain ⟨F,hF,hFa,hFb,hFh,hFv⟩ :=
    holomorphic_grid g h₁ h₂ A hA lo hi joinA B hB bot top joinB corner
  let tile (i j : ℕ) : cell t i × cell u j → X.Carrier :=
    fun p ↦ F i j (a i p.1,b j p.2)
  have htile (i j : ℕ) : ProductBoxTopology.IsBox (splittingAtlas S) (tile i j) :=
    (hF i j).plaqueBox.precomp (ha i) (hb j)
  obtain ⟨R,hR,hRt⟩ := ProductBoxTopology.grid_glue (splittingAtlas S) t u ht0 hu0 ht hu
    N M (hN N le_rfl) (hM M le_rfl) tile htile
    (fun i j y ↦ hFh i j (b j y)) (fun i j x ↦ hFv i j (a i x))
  refine ⟨R,hR,?_,?_⟩
  · intro x
    obtain ⟨i,_,hxi⟩ := covers t ht0 ht N (hN N le_rfl) x
    let xx : cell t i := ⟨x,hxi⟩
    let yy : cell u 0 := ⟨u 0,le_rfl,hu (Nat.le_succ 0)⟩
    calc R (x,0) = tile i 0 (xx,yy) := by simpa only [yy,hu0] using hRt i 0 xx yy
         _ = A i (a i xx) := hFa i (a i xx)
         _ = α x := eA i xx
  · intro y
    obtain ⟨j,_,hyj⟩ := covers u hu0 hu M (hM M le_rfl) y
    let xx : cell t 0 := ⟨t 0,le_rfl,ht (Nat.le_succ 0)⟩
    let yy : cell u j := ⟨y,hyj⟩
    calc R (0,y) = tile 0 j (xx,yy) := by simpa only [xx,ht0] using hRt 0 j xx yy
         _ = B j (b j yy) := hFb j (b j yy)
         _ = β y := eB j yy

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.EtaleGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n : ℕ} (M : ComplexManifold m) (X : ComplexManifold n)

lemma continuous_section (f : M.Carrier → X.Carrier) {U : Set M.Carrier}
    (hU : IsOpen U) (hf : MDifferentiableOn (model m) (model n) f U) :
    Continuous (sectionOf M X f hU hf) :=
  ((FunctionEtale.continuous_section f).comp continuous_subtype_val).subtype_mk _

lemma locally_represented {A : Type*} [TopologicalSpace A] {F : A → Germs M X}
    (hF : Continuous F) (a : A) :
    ∃ U : Set M.Carrier, IsOpen U ∧ base M X (F a) ∈ U ∧
      ∃ f : M.Carrier → X.Carrier, MDifferentiableOn (model m) (model n) f U ∧
        ∀ᶠ b in 𝓝 a, base M X (F b) ∈ U ∧
          (F b).val=FunctionEtale.sectionOf f (base M X (F b)) := by
  obtain ⟨U,hU,hxU,f,hf,he⟩ := (F a).property
  refine ⟨U,hU,hxU,f,hf,?_⟩
  exact (continuous_subtype_val.comp hF).continuousAt.eventually
    ((FunctionEtale.isOpen_basic f hU).mem_nhds ⟨hxU,he⟩)

end HolomorphicEtale
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

namespace FirstGerm

lemma of_factor (e : SplittingChart S) {x : X.Carrier} (hx : x ∈ e.chart.source)
    (h : Model r → X.Carrier) :
    IsFirst (S := S) (FunctionEtale.sectionOf (fun y ↦ h (e.chart y).1) x) := by
  intro d hd
  refine ⟨fun a ↦ h (e.chart (d.chart.symm (a,(d.chart x).2))).1,?_⟩
  apply FunctionEtale.section_eq.mpr
  exact (e.transition_first d hx hd).mono (fun y hy ↦ congrArg h hy)

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.GermTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

namespace FirstGerm

lemma extends_plaque (g : HolomorphicEtale.Germs X X) (hg : IsFirst (S := S) g.val)
    (e : SplittingChart S) (he : HolomorphicEtale.base X X g ∈ e.chart.source) :
    ∃ V : Set X.Carrier, IsOpen V ∧
      ∃ F : X.Carrier → X.Carrier, MDifferentiableOn (model n) (model n) F V ∧
        g.val=FunctionEtale.sectionOf F (HolomorphicEtale.base X X g) ∧
        (∀ y ∈ e.chart.source,
          (e.chart y).1=(e.chart (HolomorphicEtale.base X X g)).1 → y ∈ V) ∧
        ∀ y ∈ V, IsFirst (S := S) (FunctionEtale.sectionOf F y) := by
  obtain ⟨U,hU,hxU,f,hf,hgF⟩ := g.property
  let x := HolomorphicEtale.base X X g
  obtain ⟨h,hh⟩ := hg e he
  have hfh : f =ᶠ[𝓝 x] (fun y ↦ h (e.chart y).1) :=
    FunctionEtale.section_eq.mp (hgF.symm.trans hh)
  have hb : (e.chart x).2 ∈ ball 0 e.radius := by
    have H := e.chart.map_source he
    rw [e.product_range] at H
    exact H.2
  let P := e.firstProjection (e.chart x).2
  have hP : MDifferentiableOn (model n) (model n) P e.chart.source := e.firstProjection_holomorphic hb
  have hPx : P x=x := e.firstProjection_self he
  have hPc : ContinuousAt P x := hP.continuousOn.continuousAt (e.chart.open_source.mem_nhds he)
  let F := f ∘ P
  let V := e.chart.source ∩ P ⁻¹' U
  have hV : IsOpen V := hP.continuousOn.isOpen_inter_preimage e.chart.open_source hU
  have hPV : MapsTo P V U := fun _ hy ↦ hy.2
  refine ⟨V,hV,F,hf.comp (hP.mono inter_subset_left) hPV,?_,?_,?_⟩
  · apply hgF.trans
    apply FunctionEtale.section_eq.mpr
    have hhh : (fun y ↦ f (P y)) =ᶠ[𝓝 x] (fun y ↦ h (e.chart (P y)).1) :=
      hfh.comp_tendsto (by simpa only [ContinuousAt,hPx] using hPc)
    filter_upwards [hfh,hhh,e.chart.open_source.mem_nhds he] with y hy hy' hye
    dsimp only [F,Function.comp_apply]
    rw [hy,hy',e.firstProjection_coordinates hb hye]
  · intro y hy hxy
    refine ⟨hy,?_⟩
    have hPy : P y=x := by
      change e.chart.symm ((e.chart y).1,(e.chart x).2)=x
      rw [hxy]
      exact e.chart.left_inv he
    change P y ∈ U
    rw [hPy]
    exact hxU
  · intro y hy
    exact of_factor e hy.1 (fun a ↦ f (e.chart.symm (a,(e.chart x).2)))

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace IntervalChain
variable {E X : Type*} [TopologicalSpace E]

theorem lift_cells (p : E → X) (Q : E → Prop) (γ : I → X)
    (t : ℕ → I) (ht0 : t 0=0) (ht : Monotone t) (N : ℕ) (hN : t N=1)
    (e₀ : E) (he₀ : p e₀=γ 0) (hQ₀ : Q e₀)
    (local_lift : ∀ i e, p e=γ (t i) → Q e →
      ∃ f : cell t i → E, Continuous f ∧
        f ⟨t i,le_rfl,ht (Nat.le_succ i)⟩=e ∧
        ∀ u, p (f u)=γ u ∧ Q (f u)) :
    ∃ F : I → E, Continuous F ∧ F 0=e₀ ∧ ∀ u, p (F u)=γ u ∧ Q (F u) := by
  classical
  let State (i : ℕ) := {e : E // p e=γ (t i) ∧ Q e}
  have ex (i : ℕ) (e : State i) : ∃ f : cell t i → E, Continuous f ∧
      f ⟨t i,le_rfl,ht (Nat.le_succ i)⟩=e.val ∧ ∀ u, p (f u)=γ u ∧ Q (f u) :=
    local_lift i e.val e.property.1 e.property.2
  choose L hLc hL0 hL using ex
  let initial : State 0 := ⟨e₀,by simpa only [ht0] using he₀,hQ₀⟩
  let next (i : ℕ) (e : State i) : State (i+1) :=
    ⟨L i e ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩,hL i e _⟩
  let state : ∀ i, State i := fun i ↦ Nat.rec initial next i
  let f (i : ℕ) : cell t i → E := L i (state i)
  have seam (i : ℕ) : f i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩=
      f (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩ := by
    exact (hL0 (i+1) (state (i+1))).symm
  have cover (u : I) : ∃ i : Fin (N+1), u ∈ cell t i := by
    obtain ⟨i,hi,hu⟩ := covers t ht0 ht N hN u
    exact ⟨⟨i,by omega⟩,hu⟩
  obtain ⟨F,hF,hFr⟩ := ClosedCoverGlue.exists_glue (fun i : Fin (N+1) ↦ cell t i)
    (fun _ ↦ isClosed_Icc) cover (fun i ↦ f i) (fun i ↦ hLc i (state i))
    (fun i j u hi hj ↦ overlap t ht f seam i j u hi hj)
  have heq (i : ℕ) (u : cell t i) : F u=f i u := by
    obtain ⟨j,hj⟩ := cover u
    exact (hFr j ⟨u,hj⟩).trans (overlap t ht f seam j i u hj u.property)
  refine ⟨F,hF,?_,?_⟩
  · have H := (heq 0 ⟨t 0,le_rfl,ht (Nat.le_succ 0)⟩).trans (hL0 0 (state 0))
    change F (t 0)=e₀ at H
    simpa only [ht0] using H
  · intro u
    obtain ⟨i,hi⟩ := cover u
    rw [heq i ⟨u,hi⟩]
    exact hL i (state i) _

end IntervalChain
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]

lemma lift_chart (e : SplittingChart S) {β : A → X.Carrier}
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β)
    (hmap : ∀ a, β a ∈ e.chart.source) (a₀ : A)
    (g : HolomorphicEtale.Germs X X) (hbase : HolomorphicEtale.base X X g=β a₀)
    (hg : IsFirst (S := S) g.val) :
    ∃ G : A → HolomorphicEtale.Germs X X, Continuous G ∧ G a₀=g ∧
      ∀ a, HolomorphicEtale.base X X (G a)=β a ∧ IsFirst (S := S) (G a).val := by
  have he : HolomorphicEtale.base X X g ∈ e.chart.source := hbase ▸ hmap a₀
  obtain ⟨V,hV,F,hF,hgF,hplaque,hfirst⟩ := extends_plaque g hg e he
  have hl : IsLocallyConstant (fun a ↦ (e.chart (β a)).1) :=
    (hβ.2 e.chart ⟨e,rfl⟩).comp_continuous (continuous_id.subtype_mk hmap)
  have hbV (a : A) : β a ∈ V := by
    apply hplaque _ (hmap a)
    rw [hbase]
    exact hl.apply_eq_of_preconnectedSpace a a₀
  let G : A → HolomorphicEtale.Germs X X :=
    fun a ↦ HolomorphicEtale.sectionOf X X F hV hF ⟨β a,hbV a⟩
  refine ⟨G,(HolomorphicEtale.continuous_section X X F hV hF).comp
    (hβ.1.subtype_mk hbV),?_,fun a ↦ ⟨rfl,hfirst _ (hbV a)⟩⟩
  apply Subtype.ext
  change FunctionEtale.sectionOf F (β a₀)=g.val
  rw [←hbase]
  exact hgF.symm

lemma lift_vertical (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {β : I → X.Carrier}
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β)
    (g : HolomorphicEtale.Germs X X) (hbase : HolomorphicEtale.base X X g=β 0)
    (hg : IsFirst (S := S) g.val) :
    ∃ G : I → HolomorphicEtale.Germs X X, Continuous G ∧ G 0=g ∧
      ∀ a, HolomorphicEtale.base X X (G a)=β a ∧ IsFirst (S := S) (G a).val := by
  classical
  have ex (a : I) : ∃ e : SplittingChart S, β a ∈ e.chart.source := by
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (β a)
    exact ⟨e,he⟩
  choose e he using ex
  let U : I → Set I := fun a ↦ β ⁻¹' (e a).chart.source
  have hU (a : I) : IsOpen (U a) := (e a).chart.open_source.preimage hβ.1
  have cover : univ ⊆ ⋃ a, U a := fun a _ ↦ mem_iUnion.mpr ⟨a,he a⟩
  obtain ⟨t,ht0,ht,⟨N,hN⟩,hsub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval hU cover
  choose k hk using hsub
  apply IntervalChain.lift_cells (HolomorphicEtale.base X X) (fun g ↦ IsFirst (S := S) g.val)
    β t ht0 ht N (hN N le_rfl) g hbase hg
  intro i a ha hfirst
  let : PreconnectedSpace (Icc (t i) (t (i+1))) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact lift_chart (e (k i)) (hβ.precomp continuous_subtype_val)
    (fun u ↦ hk i u.property) ⟨t i,le_rfl,ht (Nat.le_succ i)⟩ a ha hfirst

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

namespace FirstGerm

lemma projection_first (e : SplittingChart S) (x : X.Carrier) (hx : x ∈ e.chart.source) :
    IsFirst (S := S) (projection e x hx).val :=
  of_factor e hx (fun a ↦ e.chart.symm (a,(e.chart x).2))

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Monodromy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma initial_first (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    IsFirst (S := S) (initial h₁ h₂ x).val := projection_first _ _ _

lemma lift_diagonal (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {R : I × I → X.Carrier}
    (hR : ProductBoxTopology.IsBox (splittingAtlas S) R) :
    ∃ G : I → HolomorphicEtale.Germs X X, Continuous G ∧
      G 0=initial h₁ h₂ (R (0,0)) ∧ ∀ a,
        HolomorphicEtale.base X X (G a)=R (a,a) ∧ IsFirst (S := S) (G a).val := by
  classical
  have ex (a : I) := lift_vertical h₁ h₂ (hR.vertical a)
    (initial h₁ h₂ (R (a,0))) rfl (initial_first h₁ h₂ _)
  choose F hFc hF0 hFb using ex
  have hc0 : Continuous (fun a ↦ F a 0) := by
    have he : (fun a ↦ F a 0)=(fun a ↦ initial h₁ h₂ (R (a,0))) := funext hF0
    rw [he]
    exact continuous_horizontal h₁ h₂ (hR.horizontal 0)
  let f : C(I × I,X.Carrier) := ⟨fun p ↦ R (p.2,p.1),hR.1.comp continuous_swap⟩
  have hF : Continuous (fun p : I × I ↦ F p.2 p.1) :=
    (HolomorphicEtale.localHomeomorph X X).continuous_lift (HolomorphicEtale.separated X X)
      f (funext fun p ↦ (hFb p.2 p.1).1) hc0 hFc
  exact ⟨fun a ↦ F a a,hF.comp (continuous_id.prodMk continuous_id),hF0 0,
    fun a ↦ hFb a a⟩

lemma lift_path [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {γ : I → X.Carrier} (hγ : Continuous γ) :
    ∃ G : C(I,HolomorphicEtale.Germs X X),
      G 0=initial h₁ h₂ (γ 0) ∧ HolomorphicEtale.base X X ∘ G=γ ∧
        ∀ a, IsFirst (S := S) (G a).val := by
  obtain ⟨R,hR,hdiag⟩ := path_diagonal g h₁ h₂ hγ
  obtain ⟨G,hG,hG0,hGb⟩ := lift_diagonal h₁ h₂ hR
  refine ⟨⟨G,hG⟩,?_,funext fun a ↦ (hGb a).1.trans (hdiag a),fun a ↦ (hGb a).2⟩
  rw [←hdiag 0]
  exact hG0

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting
namespace HolomorphicEtale
variable {m n k : ℕ} {M : ComplexManifold m} {X : ComplexManifold n}
    {Z : ComplexManifold k}

lemma mdifferentiable_value {F : Z.Carrier → Germs M X} (hF : Continuous F)
    {p : Z.Carrier → M.Carrier} (hp : MDifferentiable (model k) (model m) p)
    (hb : base M X ∘ F=p) : MDifferentiable (model k) (model n) (value ∘ F) := by
  intro z
  obtain ⟨U,hU,hz,f,hf,hev⟩ := locally_represented M X hF z
  have hbase (w : Z.Carrier) : base M X (F w)=p w := congrFun hb w
  have hzU : p z ∈ U := hbase z ▸ hz
  have hd := ((hf (p z) hzU).mdifferentiableAt (hU.mem_nhds hzU)).comp z (hp z)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hev] with w hw
  change value (F w)=f (p w)
  rw [value_of_section hw.2,hbase]

end HolomorphicEtale

lemma LocalBiholomorphism.mdifferentiable {n : ℕ} {X Z : ComplexManifold n}
    {p : Z.Carrier → X.Carrier} (hp : LocalBiholomorphism p) :
    MDifferentiable (model n) (model n) p := by
  intro z
  obtain ⟨e,hz,he,hd,_⟩ := hp z
  exact ((hd z hz).mdifferentiableAt (e.open_source.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.mem_of_superset (e.open_source.mem_nhds hz) (fun w hw ↦ (he w hw).symm))

end UniversalCoverSplitting
end
end

section

noncomputable section
open scoped unitInterval

lemma IsLocalHomeomorph.lift_of_simplyConnected
    {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : E → X} (hp : IsLocalHomeomorph p) (hsep : IsSeparatedMap p)
    (f : C(A,X)) (a₀ : A) (e₀ : E) (he : p e₀=f a₀)
    (ex : ∀ γ : C(I,A), γ 0=a₀ → ∃ Γ : C(I,E), Γ 0=e₀ ∧ p ∘ Γ=f.comp γ) :
    ∃! F : C(A,E), F a₀=e₀ ∧ p ∘ F=f := by
  apply hp.existsUnique_continuousMap_lifts f a₀ e₀ he ex
  intro γ γ' Γ Γ' hγ hγ' hΓ hΓ' hl hl' hend
  let q : Path a₀ (γ 1) := ⟨γ,hγ,rfl⟩
  let q' : Path a₀ (γ 1) := ⟨γ',hγ',hend.symm⟩
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic q q'
  choose L hL0 hLl using (fun t : I ↦ ex (H.eval t) (H.eval t).source)
  have h0 : (L 0 : I → E)=Γ := by
    refine hsep.eq_of_comp_eq hp.isLocallyInjective (L 0).continuous Γ.continuous ?_ 0 ?_
    · rw [hLl,hl]
      rw [H.eval_zero]
      rfl
    · exact (hL0 0).trans hΓ.symm
  have h1 : (L 1 : I → E)=Γ' := by
    refine hsep.eq_of_comp_eq hp.isLocallyInjective (L 1).continuous Γ'.continuous ?_ 0 ?_
    · rw [hLl,hl']
      rw [H.eval_one]
      rfl
    · exact (hL0 1).trans hΓ'.symm
  have heq := hp.monodromy_theorem hsep (H.map f) L
    (fun t s ↦ congrFun (hLl t) s) (fun t ↦ (hL0 t).trans (hL0 0).symm) 1
  rw [h0,h1] at heq
  exact heq.symm
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n k : ℕ} {X Z : ComplexManifold n} {A : ComplexManifold k}

lemma LocalBiholomorphism.mdifferentiable_lift {p : Z.Carrier → X.Carrier}
    (hp : LocalBiholomorphism p) {F : A.Carrier → Z.Carrier} (hF : Continuous F)
    {f : A.Carrier → X.Carrier} (hf : MDifferentiable (model k) (model n) f)
    (hl : p ∘ F=f) : MDifferentiable (model k) (model n) F := by
  intro a
  obtain ⟨e,hea,he,_,hdi⟩ := hp (F a)
  have hfa : f a=e (F a) := (congrFun hl a).symm.trans (he _ hea).symm
  have hft : f a ∈ e.target := hfa ▸ e.map_source hea
  have hd := ((hdi (f a) hft).mdifferentiableAt (e.open_target.mem_nhds hft)).comp a (hf a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hF.continuousAt (e.open_source.mem_nhds hea)] with b hb
  change F b=e.symm (f b)
  rw [←congrFun hl b]
  change F b=e.symm (p (F b))
  rw [←he _ hb]
  exact (e.left_inv hb).symm

lemma OrdinaryUniversalCover.holomorphic_lift (π : OrdinaryUniversalCover X Z)
    [SimplyConnectedSpace A.Carrier] {f : A.Carrier → X.Carrier}
    (hf : MDifferentiable (model k) (model n) f) (a : A.Carrier) (z : Z.Carrier)
    (hz : π.projection z=f a) :
    ∃ F : A.Carrier → Z.Carrier, MDifferentiable (model k) (model n) F ∧
      F a=z ∧ π.projection ∘ F=f := by
  let : LocallyPathConnectedSpace A.Carrier := ChartedSpace.locallyPathConnectedSpace (Model k) A.Carrier
  obtain ⟨F,⟨hF0,hFl⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts ⟨f,hf.continuous⟩ a z hz
  exact ⟨F,π.liftedComplexStructure.mdifferentiable_lift F.continuous hf hFl,hF0,hFl⟩

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.GlobalProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {Z : ComplexManifold n}

lemma global_germ [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (π : OrdinaryUniversalCover X Z) (o : Z.Carrier) :
    ∃ F : C(Z.Carrier,HolomorphicEtale.Germs X X),
      F o=initial h₁ h₂ (π.projection o) ∧
      HolomorphicEtale.base X X ∘ F=π.projection ∧
      ∀ z, IsFirst (S := S) (F z).val := by
  let := π.simplyConnected
  let : LocallyPathConnectedSpace Z.Carrier := ChartedSpace.locallyPathConnectedSpace (Model n) Z.Carrier
  let p : C(Z.Carrier,X.Carrier) := ⟨π.projection,π.covering.continuous⟩
  have ex (γ : C(I,Z.Carrier)) (hγ : γ 0=o) :
      ∃ Γ : C(I,HolomorphicEtale.Germs X X),
        Γ 0=initial h₁ h₂ (π.projection o) ∧ HolomorphicEtale.base X X ∘ Γ=p.comp γ ∧
        ∀ a, IsFirst (S := S) (Γ a).val := by
    obtain ⟨Γ,hΓ,hb,hfirst⟩ := lift_path g h₁ h₂ (p.comp γ).continuous
    change Γ 0=initial h₁ h₂ (π.projection (γ 0)) at hΓ
    rw [hγ] at hΓ
    exact ⟨Γ,hΓ,hb,hfirst⟩
  obtain ⟨F,⟨hF0,hFb⟩,_⟩ := _root_.OAI.IsLocalHomeomorph.lift_of_simplyConnected
    (HolomorphicEtale.localHomeomorph X X) (HolomorphicEtale.separated X X) p o (initial h₁ h₂ (π.projection o)) rfl
    (fun γ hγ ↦ (ex γ hγ).imp fun Γ h ↦ ⟨h.1,h.2.1⟩)
  refine ⟨F,hF0,hFb,?_⟩
  intro z
  let γ := PathConnectedSpace.somePath o z
  obtain ⟨Γ,hΓ0,hΓb,hΓfirst⟩ := ex γ γ.source
  have heq : (F.comp γ : I → HolomorphicEtale.Germs X X)=Γ := by
    refine (HolomorphicEtale.separated X X).eq_of_comp_eq
      (HolomorphicEtale.localHomeomorph X X).isLocallyInjective (F.continuous.comp γ.continuous) Γ.continuous ?_ 0 ?_
    · ext t
      exact (congrFun hFb (γ t)).trans (congrFun hΓb t).symm
    · change F (γ 0)=Γ 0
      rw [γ.source,hF0]
      exact hΓ0.symm
  have H := hΓfirst 1
  rw [←congrFun heq 1] at H
  change IsFirst (S := S) (F (γ 1)).val at H
  rw [γ.target] at H
  exact H

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma exists_globalProjection [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (π : OrdinaryUniversalCover X Z) (o : Z.Carrier) :
    Nonempty (GlobalProjection π o h₁ h₂) := by
  let := π.simplyConnected
  obtain ⟨F,hFo,hFb,hFfirst⟩ := global_germ g h₁ h₂ π o
  have hf : MDifferentiable (model n) (model n) (HolomorphicEtale.value ∘ F) :=
    HolomorphicEtale.mdifferentiable_value F.continuous π.liftedComplexStructure.mdifferentiable hFb
  have hfo : HolomorphicEtale.value (F o)=π.projection o := by
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (π.projection o)
    rw [hFo,initial_eq h₁ h₂ e _ he]
    exact e.firstProjection_self he
  obtain ⟨Q,hQ,hQo,hQl⟩ := π.holomorphic_lift hf o o hfo.symm
  exact ⟨⟨F,hFb,hFo,hFfirst,Q,hQ,hQo,hQl⟩⟩

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProjectionImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.image_germs [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) :
    Q.germs (Q.toFun z)=initial h₁ h₂ (π.projection (Q.toFun z)) := by
  obtain ⟨α,hα0,hα1,hα⟩ := Q.image_horizontal g z
  have h := Q.horizontal_germs α.continuous hα0 hα 1
  rwa [hα1] at h

lemma GlobalProjection.image_local [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier)
    (e : SplittingChart S) (he : π.projection (Q.toFun z) ∈ e.chart.source) :
    (π.projection ∘ Q.toFun) =ᶠ[𝓝 (Q.toFun z)]
      (e.firstProjection (e.chart (π.projection (Q.toFun z))).2 ∘ π.projection) := by
  have hev := HolomorphicEtale.value_locally Q.germs.continuous (a := Q.toFun z)
    (f := e.firstProjection (e.chart (π.projection (Q.toFun z))).2) (by
      rw [Q.image_germs g z,initial_eq h₁ h₂ e _ he]; rfl)
  rw [Q.lift]
  filter_upwards [hev] with w hw
  exact hw.trans (congrArg (e.firstProjection (e.chart (π.projection (Q.toFun z))).2)
    (congrFun Q.germs_base w))

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.RetractCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {Z : ComplexManifold n}

lemma restrict_retract_chart {Q : Z.Carrier → Z.Carrier}
    (e : OpenPartialHomeomorph Z.Carrier (Model r × Model s))
    (he : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) e e.source)
    (hei : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) e.symm e.target)
    {x : Z.Carrier} (hx : x ∈ e.source) (h0 : e x=0)
    (hl : ∀ᶠ y in 𝓝 x, Q y ∈ e.source ∧ e (Q y)=((e y).1,0)) :
    ∃ b : RetractChart Z Q r s, x ∈ b.chart.source ∧ b.chart x=0 := by
  obtain ⟨N,hN,hNo,hxN⟩ := mem_nhds_iff.mp hl
  have h0t : (0 : Model r × Model s) ∈ e.target := h0 ▸ e.map_source hx
  have he0 : e.symm 0=x := by rw [←h0,e.left_inv hx]
  have hNb : e.target ∩ e.symm ⁻¹' N ∈ 𝓝 (0 : Model r × Model s) :=
    inter_mem (e.open_target.mem_nhds h0t) ((e.symm.continuousAt h0t) (by simpa [he0] using hNo.mem_nhds hxN))
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hNb
  let V : Set (Model r × Model s) := ball 0 ε ×ˢ ball 0 ε
  have hVN : V ⊆ e.target ∩ e.symm ⁻¹' N := by
    rw [show V=ball (0 : Model r × Model s) ε from ball_prod_same _ _ _]
    exact hεN
  let b := (e.symm.restrOpen V (isOpen_ball.prod isOpen_ball)).symm
  have hbtarget : b.target=V := inter_eq_right.mpr (fun _ hy ↦ (hVN hy).1)
  have hxb : x ∈ b.source := by
    change x ∈ e.source ∧ e x ∈ V
    exact ⟨hx,by rw [h0]; exact ⟨mem_ball_self hε,mem_ball_self hε⟩⟩
  have hbproj (y : Z.Carrier) (hy : y ∈ b.source) : Q y ∈ e.source ∧ e (Q y)=((e y).1,0) := by
    apply hN
    have hh := (hVN hy.2).2
    change e.symm (e y) ∈ N at hh
    simpa only [e.left_inv hy.1] using hh
  have hbmaps : MapsTo Q b.source b.source := by
    intro y hy
    refine ⟨(hbproj y hy).1,?_⟩
    change e (Q y) ∈ V
    rw [(hbproj y hy).2]
    exact ⟨hy.2.1,mem_ball_self hε⟩
  exact ⟨⟨b,ε,hε,hbtarget,he.mono inter_subset_left,hei.mono inter_subset_left,
    hbmaps,fun y hy ↦ (hbproj y hy).2⟩,hxb,h0⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.exists_retractChart [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) {x : Z.Carrier} (hfix : Q.toFun x=x) :
    ∃ e : RetractChart Z Q.toFun r s, x ∈ e.chart.source ∧ e.chart x=0 := by
  obtain ⟨c,hxc,hc,hcd,hcdi⟩ := π.liftedComplexStructure x
  obtain ⟨d,hxd,hd0⟩ := exists_splittingChart S h₁ h₂ (π.projection x)
  let e := c.trans d.chart
  have hxe : x ∈ e.source := ⟨hxc,by change c x ∈ d.chart.source; rw [hc x hxc]; exact hxd⟩
  have he0 : e x=0 := by change d.chart (c x)=0; rw [hc x hxc,hd0]
  have he : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) e e.source :=
    d.holomorphic.comp (hcd.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hei : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) e.symm e.target :=
    hcdi.comp (d.inverse_holomorphic.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hlocal := Q.image_local g x d (by rwa [hfix])
  rw [hfix,hd0] at hlocal
  have hQx : Q.toFun x ∈ e.source := by rwa [hfix]
  apply restrict_retract_chart e he hei hxe he0
  filter_upwards [e.open_source.mem_nhds hxe,
    Q.holomorphic.continuous.continuousAt (e.open_source.mem_nhds hQx),hlocal] with y hy hQy hyeq
  refine ⟨hQy,?_⟩
  change d.chart (c (Q.toFun y))=((d.chart (c y)).1,0)
  rw [hc _ hQy.1,hc _ hy.1]
  have hyπ : π.projection y ∈ d.chart.source := by rw [←hc _ hy.1]; exact hy.2
  change π.projection (Q.toFun y)=d.firstProjection 0 (π.projection y) at hyeq
  rw [hyeq,d.firstProjection_coordinates (mem_ball_self d.radius_pos) hyπ]

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma exists_coverProductChart (π : OrdinaryUniversalCover X Z) (S : HolomorphicSplitting X r s)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S)) (x : Z.Carrier) :
    ∃ e : CoverProductChart π S, x ∈ e.chart.source ∧ e.chart x=0 := by
  obtain ⟨c,hxc,hc,hcd,hcdi⟩ := π.liftedComplexStructure x
  obtain ⟨d,hxd,hd0⟩ := exists_splittingChart S h₁ h₂ (π.projection x)
  let e := c.trans d.chart
  have hxe : x ∈ e.source := ⟨hxc,by change c x ∈ d.chart.source; rw [hc x hxc]; exact hxd⟩
  have he0 : e x=0 := by change d.chart (c x)=0; rw [hc x hxc,hd0]
  have he : MDifferentiableOn (model n) 𝓘(ℂ,Model r × Model s) e e.source :=
    d.holomorphic.comp (hcd.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hei : MDifferentiableOn 𝓘(ℂ,Model r × Model s) (model n) e.symm e.target :=
    hcdi.comp (d.inverse_holomorphic.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have h0t : (0 : Model r × Model s) ∈ e.target := he0 ▸ e.map_source hxe
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds h0t)
  let V : Set (Model r × Model s) := ball 0 ε ×ˢ ball 0 ε
  have hVU : V ⊆ e.target := by
    rw [show V=ball (0 : Model r × Model s) ε from ball_prod_same _ _ _]
    exact hεU
  let b := (e.symm.restrOpen V (isOpen_ball.prod isOpen_ball)).symm
  have hbtarget : b.target=V := inter_eq_right.mpr hVU
  have hxb : x ∈ b.source := by
    change x ∈ e.source ∧ e x ∈ V
    exact ⟨hxe,by rw [he0]; exact ⟨mem_ball_self hε,mem_ball_self hε⟩⟩
  refine ⟨⟨b,ε,hε,hbtarget,he.mono inter_subset_left,hei.mono inter_subset_left,d,?_,?_⟩,hxb,he0⟩
  · intro z hz
    rw [←hc _ hz.1.1]
    exact hz.1.2
  · intro z hz
    change d.chart (c z)=d.chart (π.projection z)
    rw [hc _ hz.1.1]

namespace CoverProductChart
variable {π : OrdinaryUniversalCover X Z} (e : CoverProductChart π S)
lemma down_inverse {p : Model r × Model s} (hp : p ∈ e.chart.target) :
    π.projection (e.chart.symm p)=e.downstairs.chart.symm p := by
  have hepi := e.coordinates _ (e.chart.map_target hp)
  rw [e.chart.right_inv hp] at hepi
  exact (e.downstairs.chart.left_inv (e.maps (e.chart.map_target hp))).symm.trans
    (congrArg e.downstairs.chart.symm hepi.symm)

end CoverProductChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.plaque_constant (Q : GlobalProjection π o h₁ h₂)
    (e : CoverProductChart π S) {a : Model r} (ha : a ∈ ball 0 e.radius)
    {b c : Model s} (hb : b ∈ ball 0 e.radius) (hc : c ∈ ball 0 e.radius) :
    Q.toFun (e.chart.symm (a,b))=Q.toFun (e.chart.symm (a,c)) := by
  let B := ball (0 : Model s) e.radius
  have hpc : PathConnectedSpace B := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_ball (0 : Model s) e.radius).isPathConnected ⟨0,mem_ball_self e.radius_pos⟩)
  let : PathConnectedSpace B := hpc
  let β := PathConnectedSpace.somePath (⟨c,hc⟩ : B) (⟨b,hb⟩ : B)
  have htar (t : I) : (a,(β t).val) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ha,(β t).property⟩
  let L : I → Z.Carrier := fun t ↦ e.chart.symm (a,(β t).val)
  have hLc : Continuous L := e.chart.symm.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_subtype_val.comp β.continuous)) htar
  have hdown (t : I) : (a,(β t).val) ∈ e.downstairs.chart.target := by
    rw [←e.chart.right_inv (htar t),e.coordinates _ (e.chart.map_target (htar t))]
    exact e.downstairs.chart.map_source (e.maps (e.chart.map_target (htar t)))
  have haD : a ∈ ball 0 e.downstairs.radius := by
    have h := hdown 0
    rw [e.downstairs.product_range] at h
    exact h.1
  let q : I → ball (0 : Model s) e.downstairs.radius := fun t ↦ ⟨(β t).val,by
    have h := hdown t
    rw [e.downstairs.product_range] at h
    exact h.2⟩
  have hq : Continuous q := (continuous_subtype_val.comp β.continuous).subtype_mk _
  have heq : π.projection ∘ L=(fun t ↦ e.downstairs.chart.symm (a,(q t).val)) := by
    ext t; exact e.down_inverse (htar t)
  have hv : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ L) := by
    rw [heq]
    exact (e.downstairs.productChart.inverse_box.vertical ⟨a,haD⟩).precomp hq
  have H := Q.vertical_constant hLc hv 1
  change Q.toFun (e.chart.symm (a,(β 1).val))=Q.toFun (e.chart.symm (a,(β 0).val)) at H
  simpa only [β.target,β.source] using H

lemma GlobalProjection.chart_factor (Q : GlobalProjection π o h₁ h₂)
    (e : CoverProductChart π S) :
    EqOn Q.toFun (fun z ↦ Q.toFun (e.chart.symm ((e.chart z).1,0))) e.chart.source := by
  intro z hz
  have ht := e.chart.map_source hz
  rw [e.product_range] at ht
  have H := Q.plaque_constant e ht.1 ht.2 (mem_ball_self e.radius_pos)
  rwa [Prod.eta,e.chart.left_inv hz] at H

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.FixedManifolds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace RetractChart
variable {n r s : ℕ} {Z : ComplexManifold n} {Q : Z.Carrier → Z.Carrier}
variable (c : Fixed Q → RetractChart Z Q r s) (hc : ∀ x, x.val ∈ (c x).chart.source)

lemma fixed_inclusion_holomorphic :
    MDifferentiable (model r) (model n) (show (fixedManifold c hc).Carrier → Z.Carrier from Subtype.val) := by
  intro x
  let Y := fixedManifold c hc
  let e := c x
  have hxs : x.val ∈ e.chart.source := hc x
  have hxt : (e.chart x.val).1 ∈ ball 0 e.radius := (e.product_range ▸ e.chart.map_source hxs).1
  rw [mdifferentiableAt_iff_source_of_mem_source (mem_chart_source (Model r) x)]
  simp only [model,modelWithCornersSelf_coe,range_id,mdifferentiableWithinAt_univ]
  have hat : ((e.chart x.val).1,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨hxt,mem_ball_self e.radius_pos⟩
  have he := (e.inverse_holomorphic _ hat).mdifferentiableAt (e.chart.open_target.mem_nhds hat)
  have hins : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s)
      (fun a : Model r ↦ (a,(0 : Model s))) (e.chart x.val).1 :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  change MDifferentiableAt (model r) (model n) (fun a ↦ (e.fixedInv a).val) (e.chart x.val).1
  apply (he.comp (e.chart x.val).1 hins).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hxt] with a ha
  change (e.fixedInv a).val=e.chart.symm (a,0)
  exact e.fixedInv_val ha

lemma fixed_projection_holomorphic (hQ : MDifferentiable (model n) (model n) Q)
    (hid : ∀ z, Q (Q z)=Q z) :
    MDifferentiable (model n) (model r)
      (show Z.Carrier → (fixedManifold c hc).Carrier from fun z ↦ ⟨Q z,hid z⟩) := by
  let q : Z.Carrier → (fixedManifold c hc).Carrier := fun z ↦ ⟨Q z,hid z⟩
  have hqc : Continuous q := hQ.continuous.subtype_mk _
  intro z
  rw [mdifferentiableAt_iff_target]
  refine ⟨hqc.continuousAt,?_⟩
  let e := c (q z)
  have hmem : Q z ∈ e.chart.source := hc (q z)
  have he := (e.holomorphic _ hmem).mdifferentiableAt (e.chart.open_source.mem_nhds hmem)
  change MDifferentiableAt (model n) (model r) (fun y ↦ (e.chart (Q y)).1) z
  exact (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp z (he.comp z (hQ z))

end RetractChart
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s k : ℕ} {X Z : ComplexManifold n} {Y : ComplexManifold k}
    {S : HolomorphicSplitting X r s} {π : OrdinaryUniversalCover X Z}

lemma CoverProductChart.surjective_derivative (e : CoverProductChart π S)
    {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Function.Surjective (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z) := by
  have ht := e.chart.map_source hz
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds ht)
  have H := mfderiv_comp (I := 𝓘(ℂ,Model r × Model s)) (I' := model n)
    (I'' := 𝓘(ℂ,Model r × Model s)) (e.chart z) (by simpa only [e.chart.left_inv hz] using he) hi
  have hid : e.chart ∘ e.chart.symm =ᶠ[𝓝 (e.chart z)] id := by
    filter_upwards [e.chart.open_target.mem_nhds ht] with p hp
    exact e.chart.right_inv hp
  rw [hid.mfderiv_eq,mfderiv_id,e.chart.left_inv hz] at H
  intro v
  refine ⟨mfderiv 𝓘(ℂ,Model r × Model s) (model n) e.chart.symm (e.chart z) v,?_⟩
  exact (congrArg (fun L : (Model r × Model s) →L[ℂ] (Model r × Model s) ↦ L v) H).symm

lemma CoverProductChart.surjective_first_derivative (e : CoverProductChart π S)
    {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Function.Surjective (mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z) := by
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hf : MDifferentiableAt 𝓘(ℂ,Model r × Model s) (model r) Prod.fst (e.chart z) :=
    mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst
  have H := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := model r) z hf he
  rw [mfderiv_eq_fderiv,hasFDerivAt_fst.fderiv] at H
  change mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z = _ at H
  rw [H]
  intro a
  obtain ⟨v,hv⟩ := e.surjective_derivative hz (a,0)
  refine ⟨v,?_⟩
  change (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).1=a
  rw [hv]

lemma CoverProductChart.surjective_factor_iff (e : CoverProductChart π S)
    {f : Z.Carrier → Y.Carrier} (hf : MDifferentiable (model n) (model k) f)
    (hfact : EqOn f (fun z ↦ f (e.chart.symm ((e.chart z).1,0))) e.chart.source)
    {z : Z.Carrier} (hz : z ∈ e.chart.source) :
    Function.Surjective (mfderiv (model n) (model k) f z) ↔
      Function.Surjective (mfderiv (model r) (model k)
        (fun a ↦ f (e.chart.symm (a,(0 : Model s)))) (e.chart z).1) := by
  let h : Model r → Y.Carrier := fun a ↦ f (e.chart.symm (a,0))
  let a := (e.chart z).1
  have ht := e.chart.map_source hz
  rw [e.product_range] at ht
  have hta : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ht.1,mem_ball_self e.radius_pos⟩
  have hi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds hta)
  have hin : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s)
      (fun a : Model r ↦ (a,(0 : Model s))) a :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hh : MDifferentiableAt (model r) (model k) h a :=
    (hf (e.chart.symm (a,0))).comp a (hi.comp a hin)
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hfirst : MDifferentiableAt (model n) (model r) (fun w ↦ (e.chart w).1) z :=
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp z he
  have H := mfderiv_comp (I := model n) (I' := model r) (I'' := model k) z hh hfirst
  have heq : f =ᶠ[𝓝 z] h ∘ (fun w ↦ (e.chart w).1) := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact hfact hw
  have hderiv : mfderiv (model n) (model k) f z =
      mfderiv (model n) (model k) (h ∘ fun w ↦ (e.chart w).1) z := heq.mfderiv_eq
  rw [hderiv, H]
  exact ⟨fun hsur ↦ fun b ↦ by
    obtain ⟨v,hv⟩ := hsur b
    exact ⟨mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z v,hv⟩,
    fun hsur ↦ hsur.comp (e.surjective_first_derivative hz)⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.vertical_reach [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) :
    ∃ β : C(I,Z.Carrier), β 0=Q.toFun z ∧ β 1=z ∧
      ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β) := by
  let := π.simplyConnected
  let γ := PathConnectedSpace.somePath o z
  obtain ⟨R,hR,hdiag⟩ := path_diagonal g h₁ h₂ (π.covering.continuous.comp γ.continuous)
  have hR0 : π.projection o=R (0,0) := by
    rw [hdiag]
    change π.projection o=π.projection (γ 0)
    rw [γ.source]
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨L,⟨hL0,hLb⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts ⟨R,hR.1⟩ (0,0) o hR0
  have hcont : Continuous (fun t : I ↦ L (t,t)) := L.continuous.comp (continuous_id.prodMk continuous_id)
  have hLdiag : (fun t : I ↦ L (t,t))=γ := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      hcont γ.continuous ?_ 0 ?_
    · ext t
      exact (congrFun hLb (t,t)).trans (hdiag t)
    · exact hL0.trans γ.source.symm
  let α : C(I,Z.Carrier) := ⟨fun t ↦ L (t,0),L.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α) := by
    have he : π.projection ∘ α=(fun t ↦ R (t,0)) := by ext t; exact congrFun hLb (t,0)
    rw [he]; exact hR.horizontal 0
  have hQα := Q.horizontal_fixed α.continuous hL0 hα 1
  have hv : ProductBoxTopology.IsVertical (splittingAtlas S) (fun t ↦ π.projection (L (1,t))) := by
    have he : (fun t ↦ π.projection (L (1,t)))=(fun t ↦ R (1,t)) := by
      ext t; exact congrFun hLb (1,t)
    rw [he]; exact hR.vertical 1
  have hQv := Q.vertical_constant (L.continuous.comp (continuous_const.prodMk continuous_id)) hv 1
  have hz : L (1,1)=z := (congrFun hLdiag 1).trans γ.target
  change Q.toFun (L (1,1))=Q.toFun (L (1,0)) at hQv
  rw [hz] at hQv
  exact ⟨⟨fun t ↦ L (1,t),L.continuous.comp (continuous_const.prodMk continuous_id)⟩,
    (hQv.trans hQα).symm,hz,hv⟩

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s k : ℕ} {X Z : ComplexManifold n} {Y : ComplexManifold k}
    {S : HolomorphicSplitting X r s} {π : OrdinaryUniversalCover X Z}

lemma surjective_mfderiv_of_rightInverse {f : Z.Carrier → Y.Carrier} {j : Y.Carrier → Z.Carrier}
    (hf : MDifferentiable (model n) (model k) f) (hj : MDifferentiable (model k) (model n) j)
    (hij : ∀ y, f (j y)=y) (y : Y.Carrier) :
    Function.Surjective (mfderiv (model n) (model k) f (j y)) := by
  have H := mfderiv_comp (I := model k) (I' := model n) (I'' := model k) y (hf _) (hj y)
  have heq : f ∘ j=id := funext hij
  rw [heq,mfderiv_id] at H
  intro v
  refine ⟨mfderiv (model k) (model n) j y v,?_⟩
  exact (congrArg (fun L : Model k →L[ℂ] Model k ↦ L v) H).symm

open scoped unitInterval

lemma surjective_along_vertical
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {f : Z.Carrier → Y.Carrier} (hf : MDifferentiable (model n) (model k) f)
    (hfact : ∀ e : CoverProductChart π S,
      EqOn f (fun z ↦ f (e.chart.symm ((e.chart z).1,0))) e.chart.source)
    {β : I → Z.Carrier} (hc : Continuous β)
    (hv : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β)) :
    ∀ t, Function.Surjective (mfderiv (model n) (model k) f (β t)) ↔
      Function.Surjective (mfderiv (model n) (model k) f (β 0)) := by
  have hl : IsLocallyConstant (fun t ↦ Function.Surjective (mfderiv (model n) (model k) f (β t))) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro t
    obtain ⟨e,he,_⟩ := exists_coverProductChart π S h₁ h₂ (β t)
    let W := (π.projection ∘ β) ⁻¹' e.downstairs.chart.source
    have htW : t ∈ W := e.maps he
    have hW : IsOpen W := e.downstairs.chart.open_source.preimage hv.1
    have hlc := (hv.2 e.downstairs.chart ⟨e.downstairs,rfl⟩).eventually_eq (⟨t,htW⟩ : W)
    obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype W ⟨t,htW⟩ _).mp hlc
    filter_upwards [hV,hW.mem_nhds htW,hc.continuousAt (e.chart.open_source.mem_nhds he)] with u huV huW hue
    apply propext
    rw [e.surjective_factor_iff hf (hfact e) hue,e.surjective_factor_iff hf (hfact e) he]
    have hh := hsub (show (⟨u,huW⟩ : W) ∈ Subtype.val ⁻¹' V from huV)
    change (e.downstairs.chart (π.projection (β u))).1=(e.downstairs.chart (π.projection (β t))).1 at hh
    rw [e.coordinates _ hue,e.coordinates _ he,hh]
  intro t
  exact (hl.apply_eq_of_preconnectedSpace t 0).to_iff

namespace FirstGerm
variable {o : Z.Carrier} {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.submersion [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂)
    (c : RetractChart.Fixed Q.toFun → RetractChart Z Q.toFun r s)
    (hc : ∀ x, x.val ∈ (c x).chart.source) (z : Z.Carrier) :
    Function.Surjective (mfderiv (model n) (model r)
      (show Z.Carrier → (RetractChart.fixedManifold c hc).Carrier from
        fun w ↦ ⟨Q.toFun w,Q.idempotent g w⟩) z) := by
  let Y := RetractChart.fixedManifold c hc
  let q : Z.Carrier → Y.Carrier := fun w ↦ ⟨Q.toFun w,Q.idempotent g w⟩
  have hq := RetractChart.fixed_projection_holomorphic c hc Q.holomorphic (Q.idempotent g)
  have hj := RetractChart.fixed_inclusion_holomorphic c hc
  have hri : ∀ y : Y.Carrier, q y.val=y := fun y ↦ Subtype.ext y.property
  have hs := surjective_mfderiv_of_rightInverse hq hj hri (q z)
  obtain ⟨β,hβ0,hβ1,hβ⟩ := Q.vertical_reach g z
  have hfact (e : CoverProductChart π S) :
      EqOn q (fun w ↦ q (e.chart.symm ((e.chart w).1,0))) e.chart.source := by
    intro w hw
    exact Subtype.ext (Q.chart_factor e hw)
  have H := surjective_along_vertical h₁ h₂ hq hfact β.continuous hβ 1
  rw [hβ0,hβ1] at H
  exact H.mpr hs

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.SwapSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

lemma HolomorphicSplitting.swap_swap (S : HolomorphicSplitting X r s) : S.swap.swap=S := by
  cases S
  simp only [HolomorphicSplitting.swap]
  congr 1
  funext x
  exact sub_sub_cancel _ _

lemma CoverProductChart.swap_derivative (e : CoverProductChart π S) {z : Z.Carrier}
    (hz : z ∈ e.chart.source) (v : Tangent Z z) :
    mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swap.chart z v=
      (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).swap := by
  let c := ContinuousLinearEquiv.prodComm ℂ (Model r) (Model s)
  have h := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := 𝓘(ℂ,Model s × Model r)) z
    (mdifferentiableAt_iff_differentiableAt.mpr c.differentiableAt)
    (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz))
  change mfderiv (model n) 𝓘(ℂ,Model s × Model r) e.swap.chart z = _ at h
  rw [mfderiv_eq_fderiv,c.hasFDerivAt.fderiv] at h
  exact congrArg (fun L : Model n →L[ℂ] (Model s × Model r) ↦ L v) h

lemma SplittingChart.cast_chart {T : HolomorphicSplitting X r s}
    (h : S=T) (e : SplittingChart S) : (h ▸ e).chart=e.chart := by
  subst T
  rfl

variable {A : Type*} [TopologicalSpace A] {f : A → X.Carrier}

lemma vertical_swap_of_horizontal
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S) f) :
    ProductBoxTopology.IsVertical (splittingAtlas S.swap) f := by
  refine ⟨hh.1,?_⟩
  rintro _ ⟨e,rfl⟩
  let d : SplittingChart S := S.swap_swap ▸ e.swap
  have H := hh.2 d.chart ⟨d,rfl⟩
  dsimp only [d] at H
  rw [SplittingChart.cast_chart] at H
  exact H

lemma vertical_of_horizontal_swap
    (hh : ProductBoxTopology.IsHorizontal (splittingAtlas S.swap) f) :
    ProductBoxTopology.IsVertical (splittingAtlas S) f := by
  have H := vertical_swap_of_horizontal hh
  rwa [S.swap_swap] at H

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProductRetracts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set unitInterval
namespace UniversalCoverSplitting

lemma simplyConnected_fixed {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    {Q : A → A} (hQc : Continuous Q) (hQ : ∀ a, Q (Q a)=Q a) :
    SimplyConnectedSpace {a : A // Q a=a} := by
  let q : A → {a : A // Q a=a} := fun a ↦ ⟨Q a,hQ a⟩
  have hq : Continuous q := hQc.subtype_mk _
  have hsur : Function.Surjective q := fun a ↦ ⟨a.val,Subtype.ext a.property⟩
  have hpc := hsur.pathConnectedSpace hq
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpc,?_⟩
  intro x y p₁ p₂
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic
    (p₁.map continuous_subtype_val) (p₂.map continuous_subtype_val)
  refine ⟨{ toFun := fun p ↦ q (H p)
            continuous_toFun := hq.comp H.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    change Q (H (0,t))=(p₁ t).val
    exact (congrArg Q (show H (0,t)=(p₁ t).val from H.map_zero_left t)).trans (p₁ t).property
  · intro t
    apply Subtype.ext
    change Q (H (1,t))=(p₂ t).val
    exact (congrArg Q (show H (1,t)=(p₂ t).val from H.map_one_left t)).trans (p₂ t).property
  · intro t u hu
    apply Subtype.ext
    change Q (H (t,u))=(p₁ u).val
    rw [H.eq_fst t hu]
    exact (p₁ u).property

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma exists_productRetracts [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (π : OrdinaryUniversalCover X Z) (o : Z.Carrier) :
    Nonempty (ProductRetracts π o h₁ h₂) := by
  classical
  obtain ⟨Q⟩ := FirstGerm.exists_globalProjection g h₁ h₂ π o
  obtain ⟨R⟩ := FirstGerm.exists_globalProjection g h₂ (integrable_swap_complement h₁) π o
  have hc (x : RetractChart.Fixed Q.toFun) := Q.exists_retractChart g x.property
  have hd (x : RetractChart.Fixed R.toFun) := R.exists_retractChart g x.property
  choose c hc₁ hc₂ using hc
  choose d hd₁ hd₂ using hd
  exact ⟨⟨Q,R,c,hc₁,d,hd₁⟩⟩

namespace ProductRetracts
variable (P : ProductRetracts π o h₁ h₂)

variable [CompactSpace X.Carrier] (g : KahlerMetric X)

lemma q₁_holomorphic : MDifferentiable (model n) (model r) (P.q₁ g) :=
  RetractChart.fixed_projection_holomorphic P.firstCharts P.first_mem P.first.holomorphic
    (P.first.idempotent g)
lemma q₂_holomorphic : MDifferentiable (model n) (model s) (P.q₂ g) :=
  RetractChart.fixed_projection_holomorphic P.secondCharts P.second_mem P.second.holomorphic
    (P.second.idempotent g)
lemma pair_holomorphic : MDifferentiable (model n) ((model r).prod (model s)) (P.pair g) :=
  (P.q₁_holomorphic g).prodMk (P.q₂_holomorphic g)

lemma q₁_submersion (z : Z.Carrier) : Function.Surjective (mfderiv (model n) (model r) (P.q₁ g) z) :=
  P.first.submersion g P.firstCharts P.first_mem z
lemma q₂_submersion (z : Z.Carrier) : Function.Surjective (mfderiv (model n) (model s) (P.q₂ g) z) :=
  P.second.submersion g P.secondCharts P.second_mem z

lemma q₁_factor (e : CoverProductChart π S) :
    EqOn (P.q₁ g) (fun w ↦ P.q₁ g (e.chart.symm ((e.chart w).1,0))) e.chart.source := by
  intro w hw
  exact Subtype.ext (P.first.chart_factor e hw)
lemma q₂_factor (e : CoverProductChart π S) :
    EqOn (P.q₂ g) (fun w ↦ P.q₂ g (e.chart.symm (0,(e.chart w).2))) e.chart.source := by
  intro w hw
  exact Subtype.ext (P.second.chart_factor e.swap hw)

include g in
lemma simplyConnected_first : SimplyConnectedSpace P.Y₁.Carrier := by
  let := π.simplyConnected
  exact simplyConnected_fixed P.first.holomorphic.continuous (P.first.idempotent g)
include g in
lemma simplyConnected_second : SimplyConnectedSpace P.Y₂.Carrier := by
  let := π.simplyConnected
  exact simplyConnected_fixed P.second.holomorphic.continuous (P.second.idempotent g)

end ProductRetracts
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {Y : ComplexManifold r}
    {S : HolomorphicSplitting X r s} {π : OrdinaryUniversalCover X Z}

lemma CoverProductChart.factor_kernel (e : CoverProductChart π S)
    {f : Z.Carrier → Y.Carrier} (hf : MDifferentiable (model n) (model r) f)
    (hfact : EqOn f (fun z ↦ f (e.chart.symm ((e.chart z).1,0))) e.chart.source)
    {z : Z.Carrier} (hz : z ∈ e.chart.source)
    (hsur : Function.Surjective (mfderiv (model n) (model r) f z)) (v : Tangent Z z) :
    mfderiv (model n) (model r) f z v=0 ↔
      (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).1=0 := by
  let h : Model r → Y.Carrier := fun a ↦ f (e.chart.symm (a,0))
  let a := (e.chart z).1
  have ht := e.chart.map_source hz
  rw [e.product_range] at ht
  have hta : (a,(0 : Model s)) ∈ e.chart.target := by
    rw [e.product_range]; exact ⟨ht.1,mem_ball_self e.radius_pos⟩
  have hi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds hta)
  have hin : MDifferentiableAt (model r) 𝓘(ℂ,Model r × Model s)
      (fun a : Model r ↦ (a,(0 : Model s))) a :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have hh : MDifferentiableAt (model r) (model r) h a :=
    (hf (e.chart.symm (a,0))).comp a (hi.comp a hin)
  have he := e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds hz)
  have hfirst : MDifferentiableAt (model n) (model r) (fun w ↦ (e.chart w).1) z :=
    (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp z he
  have H := mfderiv_comp (I := model n) (I' := model r) (I'' := model r) z hh hfirst
  have heq : f =ᶠ[𝓝 z] h ∘ (fun w ↦ (e.chart w).1) := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact hfact hw
  have hderiv : mfderiv (model n) (model r) f z =
      mfderiv (model n) (model r) (h ∘ fun w ↦ (e.chart w).1) z := heq.mfderiv_eq
  rw [←hderiv] at H
  have hhsur := (e.surjective_factor_iff hf hfact hz).mp hsur
  have hhinj : Function.Injective (mfderiv (model r) (model r) h a) :=
    (LinearMap.injective_iff_surjective (f := (show Model r →ₗ[ℂ] Model r from (mfderiv (model r) (model r) h a).toLinearMap))).mpr hhsur
  have Hfirst := mfderiv_comp (I := model n) (I' := 𝓘(ℂ,Model r × Model s))
    (I'' := model r) z (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst) he
  rw [mfderiv_eq_fderiv,hasFDerivAt_fst.fderiv] at Hfirst
  change mfderiv (model n) (model r) (fun w ↦ (e.chart w).1) z = _ at Hfirst
  rw [H,Hfirst]
  change mfderiv (model r) (model r) h a ((mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v).1)=0 ↔ _
  exact map_eq_zero_iff _ hhinj

end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProductLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ,F) ∞ N]

lemma holomorphic_local_chart_of_bijective {f : M → N}
    (hf : MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) f) {p : M}
    (hbij : Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f p)) :
    ∃ e : OpenPartialHomeomorph M N, p ∈ e.source ∧ EqOn e f e.source ∧
      e.MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) := by
  let c := chartAt E p
  let d := chartAt F (f p)
  have hc : c.MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,E) := mdifferentiable_chart p
  have hd : d.MDifferentiable 𝓘(ℂ,F) 𝓘(ℂ,F) := mdifferentiable_chart (f p)
  have hpc : p ∈ c.source := mem_chart_source E p
  have hpd : f p ∈ d.source := mem_chart_source F (f p)
  let U : Set E := c.target ∩ (f ∘ c.symm) ⁻¹' d.source
  have hUc : IsOpen U := (hf.continuous.comp_continuousOn c.symm.continuousOn).isOpen_inter_preimage
    c.open_target d.open_source
  have hpU : c p ∈ U := ⟨c.map_source hpc,by change f (c.symm (c p)) ∈ d.source; rw [c.left_inv hpc]; exact hpd⟩
  let H : E → F := d ∘ f ∘ c.symm
  have hH : DifferentiableOn ℂ H U := mdifferentiableOn_iff_differentiableOn.mp
    (hd.1.comp ((hf.mdifferentiableOn (s := univ)).comp (hc.2.mono inter_subset_left) (fun _ _ ↦ mem_univ _))
      (fun _ hz ↦ hz.2))
  have hD : Function.Bijective (fderiv ℂ H (c p)) := by
    have hci := hc.mdifferentiableAt_symm (c.map_source hpc)
    have hfp := hf p
    have hdp := hd.mdifferentiableAt hpd
    have hcomp := mfderiv_comp (I := 𝓘(ℂ,E)) (I' := 𝓘(ℂ,E)) (I'' := 𝓘(ℂ,F))
      (c p) (by simpa only [c.left_inv hpc] using hfp) hci
    have hfp' : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,F) f (c.symm (c p)) := by
      simpa only [c.left_inv hpc] using hfp
    have hfc : MDifferentiableAt 𝓘(ℂ,E) 𝓘(ℂ,F) (f ∘ c.symm) (c p) := hfp'.comp (c p) hci
    have hdp' : MDifferentiableAt 𝓘(ℂ,F) 𝓘(ℂ,F) d ((f ∘ c.symm) (c p)) := by
      simpa only [Function.comp_apply,c.left_inv hpc] using hdp
    have hcomp2 := mfderiv_comp (I := 𝓘(ℂ,E)) (I' := 𝓘(ℂ,F)) (I'' := 𝓘(ℂ,F))
      (c p) hdp' hfc
    rw [mfderiv_eq_fderiv] at hcomp2
    change fderiv ℂ H (c p)=_ at hcomp2
    rw [hcomp2,hcomp]
    have hbij' : Function.Bijective (mfderiv 𝓘(ℂ,E) 𝓘(ℂ,F) f (c.symm (c p))) := by
      rw [c.left_inv hpc]
      exact hbij
    have hpd' : f (c.symm (c p)) ∈ d.source := by rwa [c.left_inv hpc]
    exact (hd.mfderiv_bijective hpd').comp (hbij'.comp (hc.symm.mfderiv_bijective (c.map_source hpc)))
  let L : E ≃L[ℂ] F := (LinearEquiv.ofBijective (fderiv ℂ H (c p)).toLinearMap hD).toContinuousLinearEquiv
  have hL : HasFDerivAt H (L : E →L[ℂ] F) (c p) := (hH.differentiableAt (hUc.mem_nhds hpU)).hasFDerivAt
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨b,hb,hpb,hbU,hbd,hbdi⟩ := exists_holomorphic_ift_chart hUc
    (finite_holomorphic_contDiffOn_one hUc hH) hpU L hL
  have hbM : b.MDifferentiable 𝓘(ℂ,E) 𝓘(ℂ,F) :=
    ⟨mdifferentiableOn_iff_differentiableOn.mpr (hbd.differentiableOn (by norm_num)),
      mdifferentiableOn_iff_differentiableOn.mpr (hbdi.differentiableOn (by norm_num))⟩
  let e := (c.trans b).trans d.symm
  have heq (x : M) (hx : x ∈ e.source) : e x=f x := by
    change d.symm (b (c x))=f x
    rw [hb]
    change d.symm (d (f (c.symm (c x))))=f x
    rw [c.left_inv hx.1.1]
    have hh : f x ∈ d.source := by
      have h := (hbU hx.1.2).2
      change f (c.symm (c x)) ∈ d.source at h
      rwa [c.left_inv hx.1.1] at h
    exact d.left_inv hh
  have hpe : p ∈ e.source := by
    refine ⟨⟨hpc,hpb⟩,?_⟩
    change b (c p) ∈ d.target
    rw [hb]
    change d (f (c.symm (c p))) ∈ d.target
    rw [c.left_inv hpc]
    exact d.map_source hpd
  exact ⟨e,hpe,heq,(hc.trans hbM).trans hd.symm⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace ProductRetracts
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

lemma pair_derivative_bijective (z : Z.Carrier) :
    Function.Bijective (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z) := by
  obtain ⟨e,hz,_⟩ := exists_coverProductChart π S h₁ h₂ z
  have heDiff : e.chart.MDifferentiable (model n) 𝓘(ℂ,Model r × Model s) :=
    ⟨e.holomorphic,e.inverse_holomorphic⟩
  have hd := mfderiv_prodMk (P.q₁_holomorphic g z) (P.q₂_holomorphic g z)
  change mfderiv (model n) ((model r).prod (model s)) (P.pair g) z = _ at hd
  have hinj : Function.Injective (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    rw [hd] at hv
    have hv₁ := congrArg Prod.fst hv
    have hv₂ := congrArg Prod.snd hv
    have he₁ := (e.factor_kernel (P.q₁_holomorphic g) (P.q₁_factor g e) hz
      (P.q₁_submersion g z) v).mp hv₁
    have he₂ := (e.swap.factor_kernel (P.q₂_holomorphic g) (P.q₂_factor g e)
      hz (P.q₂_submersion g z) v).mp hv₂
    rw [e.swap_derivative hz v] at he₂
    have he : mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v=0 := Prod.ext he₁ he₂
    exact heDiff.mfderiv_injective hz
      (he.trans (map_zero _).symm)
  refine ⟨hinj,?_⟩
  have hb := heDiff.mfderiv_bijective hz
  have hfin : Module.finrank ℂ (Model n)=Module.finrank ℂ (Model r × Model s) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective
      (show Model n →ₗ[ℂ] (Model r × Model s) from (mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z).toLinearMap) hb)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (show Model n →ₗ[ℂ] (Model r × Model s) from
      (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z).toLinearMap))).mp hinj

lemma pair_local_chart (z : Z.Carrier) :
    ∃ e : OpenPartialHomeomorph Z.Carrier (P.Y₁.Carrier × P.Y₂.Carrier),
      z ∈ e.source ∧ EqOn e (P.pair g) e.source ∧
      e.MDifferentiable (model n) ((model r).prod (model s)) := by
  let : ChartedSpace (Model r × Model s) (P.Y₁.Carrier × P.Y₂.Carrier) :=
    prodChartedSpace (Model r) P.Y₁.Carrier (Model s) P.Y₂.Carrier
  have hmodel : (model r).prod (model s)=𝓘(ℂ,Model r × Model s) := modelWithCornersSelf_prod.symm
  let : IsManifold 𝓘(ℂ,Model r × Model s) ∞ (P.Y₁.Carrier × P.Y₂.Carrier) := by
    rw [←hmodel]
    exact IsManifold.prod (I := model r) (I' := model s) P.Y₁.Carrier P.Y₂.Carrier
  have hf : MDifferentiable (model n) 𝓘(ℂ,Model r × Model s) (P.pair g) := by
    rw [←hmodel]; exact P.pair_holomorphic g
  have hb : Function.Bijective (mfderiv (model n) 𝓘(ℂ,Model r × Model s) (P.pair g) z) := by
    rw [←hmodel]; exact P.pair_derivative_bijective g z
  obtain ⟨e,he,heq,hd⟩ := holomorphic_local_chart_of_bijective hf hb
  exact ⟨e,he,heq,by rw [hmodel]; exact hd⟩

lemma pair_isLocalHomeomorph : IsLocalHomeomorph (P.pair g) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro z
  obtain ⟨e,he,heq,_⟩ := P.pair_local_chart g z
  refine ⟨e.source,e.open_source.mem_nhds he,?_⟩
  have h : e.source.domRestrict (P.pair g)=e.source.domRestrict e := funext (fun x ↦ (heq x.property).symm)
  rw [h]
  exact e.isOpenEmbedding_restrict

end ProductRetracts
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.PathLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

lemma cover_path_axes [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α β : I → Z.Carrier} (hcα : Continuous α) (hcβ : Continuous β)
    (hα : ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α))
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) (π.projection ∘ β))
    (hbase : α 0=β 0) :
    ∃ L : C(I × I,Z.Carrier),
      ProductBoxTopology.IsBox (splittingAtlas S) (π.projection ∘ L) ∧
      (∀ t, L (t,0)=α t) ∧ (∀ t, L (0,t)=β t) := by
  obtain ⟨R,hR,ha,hb⟩ := path_axes g h₁ h₂ hα hβ (congrArg π.projection hbase)
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨L,⟨hL0,hLb⟩,_⟩ := π.covering.existsUnique_continuousMap_lifts
    ⟨R,hR.1⟩ (0,0) (α 0) (ha 0).symm
  have hA : (fun t : I ↦ L (t,0))=α := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (L.continuous.comp (continuous_id.prodMk continuous_const)) hcα ?_ 0 hL0
    ext t
    exact (congrFun hLb (t,0)).trans (ha t)
  have hB : (fun t : I ↦ L (0,t))=β := by
    refine π.covering.isSeparatedMap.eq_of_comp_eq π.covering.isLocalHomeomorph.isLocallyInjective
      (L.continuous.comp (continuous_const.prodMk continuous_id)) hcβ ?_ 0 (hL0.trans hbase)
    ext t
    exact (congrFun hLb (0,t)).trans (hb t)
  exact ⟨L,by rw [hLb]; exact hR,congrFun hA,congrFun hB⟩

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology Metric
open scoped Manifold
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    {A : Type*} [TopologicalSpace A]

lemma GlobalProjection.fixed_path_horizontal [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) {α : A → Z.Carrier} (hc : Continuous α)
    (hfix : ∀ t, Q.toFun (α t)=α t) :
    ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ α) := by
  refine ⟨π.covering.continuous.comp hc,?_⟩
  rintro _ ⟨e,rfl⟩
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t
  have ht : π.projection (α t.val) ∈ e.chart.source := t.property
  have hloc := Q.image_local g (α t.val) e (by rwa [hfix])
  rw [hfix] at hloc
  have hct : Continuous (fun u : {u : A // (π.projection ∘ α) u ∈ e.chart.source} ↦ α u.val) :=
    hc.comp continuous_subtype_val
  have hb : (e.chart (π.projection (α t.val))).2 ∈ ball 0 e.radius := by
    have H := e.chart.map_source ht
    rw [e.product_range] at H
    exact H.2
  filter_upwards [hct.continuousAt.preimage_mem_nhds hloc] with u hu
  change π.projection (Q.toFun (α u.val))=
    e.firstProjection (e.chart (π.projection (α t.val))).2 (π.projection (α u.val)) at hu
  rw [hfix] at hu
  have hh := congrArg (fun x ↦ (e.chart x).2) hu
  have huE : π.projection (α u.val) ∈ e.chart.source := u.property
  rw [e.firstProjection_coordinates hb huE] at hh
  exact hh

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}

lemma GlobalProjection.horizontal_lift [CompactSpace X.Carrier] (g : KahlerMetric X)
    (Q : GlobalProjection π o h₁ h₂) (z : Z.Carrier) {α : I → Z.Carrier}
    (hcα : Continuous α) (hfix : ∀ t, Q.toFun (α t)=α t) (hα0 : α 0=Q.toFun z) :
    ∃ A : C(I,Z.Carrier), A 0=z ∧
      ProductBoxTopology.IsHorizontal (splittingAtlas S) (π.projection ∘ A) ∧
      ∀ t, Q.toFun (A t)=α t := by
  obtain ⟨β,hβ0,hβ1,hβ⟩ := Q.vertical_reach g z
  obtain ⟨L,hL,ha,hb⟩ := cover_path_axes g h₁ h₂ hcα β.continuous
    (Q.fixed_path_horizontal g hcα hfix) hβ (hα0.trans hβ0.symm)
  let A : C(I,Z.Carrier) := ⟨fun t ↦ L (t,1),L.continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨A,(hb 1).trans hβ1,hL.horizontal 1,?_⟩
  intro t
  have H := Q.vertical_constant (L.continuous.comp (continuous_const.prodMk continuous_id)) (hL.vertical t) 1
  change Q.toFun (L (t,1))=Q.toFun (L (t,0)) at H
  exact H.trans ((congrArg Q.toFun (ha t)).trans (hfix t))

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace ProductRetracts
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

lemma pair_path_lift (z : Z.Carrier) (γ : C(I,P.Y₁.Carrier × P.Y₂.Carrier))
    (hγ : γ 0=P.pair g z) :
    ∃ L : C(I,Z.Carrier), L 0=z ∧ P.pair g ∘ L=γ := by
  have hα0 : (γ 0).1.val=P.first.toFun z := congrArg (fun y : P.Y₁.Carrier × P.Y₂.Carrier ↦ y.1.val) hγ
  have hβ0 : (γ 0).2.val=P.second.toFun z := congrArg (fun y : P.Y₁.Carrier × P.Y₂.Carrier ↦ y.2.val) hγ
  obtain ⟨A,hA0,hA,hAeq⟩ := P.first.horizontal_lift g z
    (continuous_subtype_val.comp γ.continuous.fst) (fun t ↦ (γ t).1.property) hα0
  obtain ⟨B,hB0,hB,hBeq⟩ := P.second.horizontal_lift g z
    (continuous_subtype_val.comp γ.continuous.snd) (fun t ↦ (γ t).2.property) hβ0
  obtain ⟨R,hR,ha,hb⟩ := cover_path_axes g h₁ h₂ A.continuous B.continuous hA
    (vertical_of_horizontal_swap hB) (hA0.trans hB0.symm)
  let L : C(I,Z.Carrier) := ⟨fun t ↦ R (t,t),R.continuous.comp (continuous_id.prodMk continuous_id)⟩
  refine ⟨L,(ha 0).trans hA0,?_⟩
  funext t
  apply Prod.ext
  · apply Subtype.ext
    have H := P.first.vertical_constant (R.continuous.comp (continuous_const.prodMk continuous_id))
      (hR.vertical t) t
    change P.first.toFun (R (t,t))=P.first.toFun (R (t,0)) at H
    exact H.trans ((congrArg P.first.toFun (ha t)).trans (hAeq t))
  · apply Subtype.ext
    have H := P.second.vertical_constant (R.continuous.comp (continuous_id.prodMk continuous_const))
      (vertical_swap_of_horizontal (hR.horizontal t)) t
    change P.second.toFun (R (t,t))=P.second.toFun (R (0,t)) at H
    exact H.trans ((congrArg P.second.toFun (hb t)).trans (hBeq t))

end ProductRetracts
end UniversalCoverSplitting
end
end

section

noncomputable section
namespace UniversalCoverSplitting
lemma simplyConnected_product {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [SimplyConnectedSpace A] [SimplyConnectedSpace B] : SimplyConnectedSpace (A × B) := by
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance,?_⟩
  intro x y p₁ p₂
  obtain ⟨H₁⟩ := SimplyConnectedSpace.paths_homotopic (p₁.map continuous_fst) (p₂.map continuous_fst)
  obtain ⟨H₂⟩ := SimplyConnectedSpace.paths_homotopic (p₁.map continuous_snd) (p₂.map continuous_snd)
  refine ⟨{ toFun := fun z ↦ (H₁ z,H₂ z)
            continuous_toFun := H₁.continuous.prodMk H₂.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact Prod.ext (H₁.map_zero_left t) (H₂.map_zero_left t)
  · intro t
    exact Prod.ext (H₁.map_one_left t) (H₂.map_one_left t)
  · intro t u hu
    exact Prod.ext (H₁.eq_fst t hu) (H₂.eq_fst t hu)
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Biholomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
namespace ProductRetracts
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

lemma pair_homeomorph :
    ∃ Φ : Z.Carrier ≃ₜ (P.Y₁.Carrier × P.Y₂.Carrier), (Φ : Z.Carrier → _)=P.pair g := by
  let := π.connected
  let := P.simplyConnected_first g
  let := P.simplyConnected_second g
  let : SimplyConnectedSpace (P.Y₁.Carrier × P.Y₂.Carrier) := simplyConnected_product
  let : LocallyPathConnectedSpace P.Y₁.Carrier := ChartedSpace.locallyPathConnectedSpace (Model r) P.Y₁.Carrier
  let : LocallyPathConnectedSpace P.Y₂.Carrier := ChartedSpace.locallyPathConnectedSpace (Model s) P.Y₂.Carrier
  let f : C(P.Y₁.Carrier × P.Y₂.Carrier,P.Y₁.Carrier × P.Y₂.Carrier) := ContinuousMap.id _
  have hp := P.pair_isLocalHomeomorph g
  have hsep := T2Space.isSeparatedMap (P.pair g)
  obtain ⟨F,⟨hF0,hFl⟩,_⟩ := _root_.OAI.IsLocalHomeomorph.lift_of_simplyConnected hp hsep f (P.pair g o) o rfl
    (fun γ hγ ↦ P.pair_path_lift g o γ hγ)
  have hleft : (F : _ → Z.Carrier) ∘ P.pair g=id := by
    refine hsep.eq_of_comp_eq hp.isLocallyInjective (F.continuous.comp hp.continuous) continuous_id ?_ o hF0
    funext z
    exact congrFun hFl (P.pair g z)
  let Φ : Z.Carrier ≃ₜ (P.Y₁.Carrier × P.Y₂.Carrier) :=
    { toFun := P.pair g
      invFun := F
      left_inv := congrFun hleft
      right_inv := congrFun hFl
      continuous_toFun := hp.continuous
      continuous_invFun := F.continuous }
  exact ⟨Φ,rfl⟩

lemma pair_biholomorph :
    ∃ Φ : Z.Carrier ≃ₜ (P.Y₁.Carrier × P.Y₂.Carrier), (Φ : Z.Carrier → _)=P.pair g ∧
      MDifferentiable (model n) ((model r).prod (model s)) Φ ∧
      MDifferentiable ((model r).prod (model s)) (model n) Φ.symm := by
  obtain ⟨Φ,hΦ⟩ := P.pair_homeomorph g
  refine ⟨Φ,hΦ,by rw [hΦ]; exact P.pair_holomorphic g,?_⟩
  intro y
  obtain ⟨e,he,heq,hd⟩ := P.pair_local_chart g (Φ.symm y)
  have hye : e (Φ.symm y)=y := (heq he).trans (by rw [←hΦ]; exact Φ.apply_symm_apply y)
  have ht : y ∈ e.target := hye ▸ e.map_source he
  have hi := hd.mdifferentiableAt_symm ht
  apply hi.congr_of_eventuallyEq
  filter_upwards [Φ.symm.continuous.continuousAt (e.open_source.mem_nhds he)] with w hw
  have hew : e (Φ.symm w)=w := (heq hw).trans (by rw [←hΦ]; exact Φ.apply_symm_apply w)
  exact (e.left_inv hw).symm.trans (congrArg e.symm hew)

end ProductRetracts
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}

lemma CoverProductChart.derivative_down (e : CoverProductChart π S) {z : Z.Carrier}
    (hz : z ∈ e.chart.source) (v : Tangent Z z) :
    mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v=
      mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.downstairs.chart (π.projection z)
        (mfderiv (model n) (model n) π.projection z v) := by
  have heq : (e.chart : Z.Carrier → _) =ᶠ[𝓝 z] e.downstairs.chart ∘ π.projection := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact e.coordinates w hw
  have H := mfderiv_comp (I := model n) (I' := model n) (I'' := 𝓘(ℂ,Model r × Model s)) z
    (e.downstairs.holomorphic.mdifferentiableAt (e.downstairs.chart.open_source.mem_nhds (e.maps hz)))
    (π.liftedComplexStructure.mdifferentiable z)
  have hderiv : mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z =
      mfderiv (model n) 𝓘(ℂ,Model r × Model s) (e.downstairs.chart ∘ π.projection) z :=
    heq.mfderiv_eq
  rw [←hderiv] at H
  exact congrArg (fun L : Model n →L[ℂ] (Model r × Model s) ↦ L v) H

namespace ProductRetracts
variable {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)

lemma first_kernel (z : Z.Carrier) (v : Tangent Z z) :
    mfderiv (model n) (model r) (P.q₁ g) z v=0 ↔
      S.projection (π.projection z) (mfderiv (model n) (model n) π.projection z v)=0 := by
  obtain ⟨e,hz,_⟩ := exists_coverProductChart π S h₁ h₂ z
  rw [e.factor_kernel (P.q₁_holomorphic g) (P.q₁_factor g e) hz (P.q₁_submersion g z) v,
    e.derivative_down hz v]
  exact (e.downstairs.vertical _ (e.maps hz) _).symm

lemma second_kernel (z : Z.Carrier) (v : Tangent Z z) :
    mfderiv (model n) (model s) (P.q₂ g) z v=0 ↔
      S.projection (π.projection z) (mfderiv (model n) (model n) π.projection z v)=
        mfderiv (model n) (model n) π.projection z v := by
  obtain ⟨e,hz,_⟩ := exists_coverProductChart π S h₁ h₂ z
  rw [e.swap.factor_kernel (P.q₂_holomorphic g) (P.q₂_factor g e) hz (P.q₂_submersion g z) v,
    e.swap_derivative hz v,e.derivative_down hz v]
  exact (e.downstairs.horizontal _ (e.maps hz) _).symm

lemma first_tangent (z : Z.Carrier) :
    Submodule.map (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.range (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.snd ℂ (Model r) (Model s)).toLinearMap := by
  have hd := mfderiv_prodMk (P.q₁_holomorphic g z) (P.q₂_holomorphic g z)
  change mfderiv (model n) ((model r).prod (model s)) (P.pair g) z=_ at hd
  have hmem (v : Tangent Z z) :
      mfderiv (model n) (model n) π.projection z v ∈ LinearMap.range (S.projection (π.projection z)).toLinearMap ↔
      mfderiv (model n) (model s) (P.q₂ g) z v=0 := by
    rw [P.second_kernel g]
    constructor
    · rintro ⟨w,hw⟩
      rw [←hw]
      exact S.idempotent _ _
    · intro h
      exact ⟨_,h⟩
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z v).2=0
    rw [hd]
    exact (hmem v).mp hv
  · intro hw
    obtain ⟨v,hv⟩ := (P.pair_derivative_bijective g z).2 w
    refine ⟨v,(hmem v).mpr ?_,hv⟩
    change w.2=0 at hw
    rw [←hv,hd] at hw
    exact hw

lemma second_tangent (z : Z.Carrier) :
    Submodule.map (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.ker (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.fst ℂ (Model r) (Model s)).toLinearMap := by
  have hd := mfderiv_prodMk (P.q₁_holomorphic g z) (P.q₂_holomorphic g z)
  change mfderiv (model n) ((model r).prod (model s)) (P.pair g) z=_ at hd
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z v).1=0
    rw [hd]
    exact (P.first_kernel g z v).mpr hv
  · intro hw
    obtain ⟨v,hv⟩ := (P.pair_derivative_bijective g z).2 w
    refine ⟨v,(P.first_kernel g z v).mp ?_,hv⟩
    change w.1=0 at hw
    rw [←hv,hd] at hw
    exact hw

end ProductRetracts
end UniversalCoverSplitting
end
end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
universe u v
variable {n r₁ r₂ : ℕ}

theorem main_oai (X : ComplexManifold.{u} n) [CompactSpace X.Carrier]
    [ConnectedSpace X.Carrier] (hn : 2 ≤ n) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (g : KahlerMetric X) (S : HolomorphicSplitting X r₁ r₂)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (Z : ComplexManifold.{v} n) (π : OrdinaryUniversalCover X Z) :
    ∃ (Y₁ : ComplexManifold.{v} r₁) (Y₂ : ComplexManifold.{v} r₂),
      ConnectedSpace Y₁.Carrier ∧ ConnectedSpace Y₂.Carrier ∧
      SimplyConnectedSpace Y₁.Carrier ∧ SimplyConnectedSpace Y₂.Carrier ∧
      CompatibleProduct S π Y₁ Y₂ := by
  have _ := hn
  have _ := hr₁
  have _ := hr₂
  let := π.connected
  let o : Z.Carrier := Classical.choice inferInstance
  obtain ⟨P⟩ := exists_productRetracts g h₁ h₂ π o
  let := P.simplyConnected_first g
  let := P.simplyConnected_second g
  refine ⟨P.Y₁,P.Y₂,inferInstance,inferInstance,inferInstance,inferInstance,?_⟩
  obtain ⟨Φ,hΦ,hd,hdi⟩ := P.pair_biholomorph g
  refine ⟨Φ,hd,hdi,?_,?_⟩
  · rw [hΦ]
    exact P.first_tangent g
  · rw [hΦ]
    exact P.second_tangent g

end UniversalCoverSplitting
end
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.UniversalCoverSplitting.main_oai.{u, v} := @OAI.UniversalCoverSplitting.main_oai.{u, v}
