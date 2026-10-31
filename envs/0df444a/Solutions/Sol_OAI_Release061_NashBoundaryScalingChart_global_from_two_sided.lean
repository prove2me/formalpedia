-- Prove2me | solution 1 for OAI.Release061.NashBoundaryScalingChart.global_from_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:08:14.197338+00:00
-- url     : https://prove2.me/submissions/35657fa8-9469-498e-98dc-a1d45f02ce69

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ZeroLocusPolynomialSmooth
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem smoothAtSubset_restrict_open {n : ℕ} {S T : Set (Affine n)}
    (hST : S ⊆ T) (hS : IsOpen ((Subtype.val : T → Affine n) ⁻¹' S))
    {q : Affine n} (hq : q ∈ S) (hqT : SmoothAtSubset T q) : SmoothAtSubset S q := by
  classical
  obtain ⟨m,W,hWT,hW,hqW,D,hD,⟨e⟩⟩ := hqT
  let Z : Set W := (Subtype.val : W → Affine n) ⁻¹' S
  have hZ : IsOpen Z := hS.preimage (Topology.IsEmbedding.inclusion hWT).continuous
  let D' := (Subtype.val : D → Affine m) '' (e.toHomeomorph '' Z)
  have hD' : IsOpen D' := hD.isOpenMap_subtype_val _ (e.toHomeomorph.isOpenMap _ hZ)
  have hD'D : D' ⊆ D := by rintro y ⟨z,_,rfl⟩; exact z.property
  have he : ∀ x : W, x.val ∈ W ∩ S ↔ (e.toHomeomorph x).val ∈ D' := by
    intro x
    constructor
    · intro hx
      exact ⟨e.toHomeomorph x,⟨x,hx.2,rfl⟩,rfl⟩
    · rintro ⟨y,⟨z,hz,hzy⟩,hy⟩
      have hzx : z = x := e.toHomeomorph.injective (hzy.trans (Subtype.ext hy))
      exact ⟨x.property,hzx ▸ hz⟩
  have hW' : IsOpen ((Subtype.val : S → Affine n) ⁻¹' (W ∩ S)) := by
    have hpre := hW.preimage (Topology.IsEmbedding.inclusion hST).continuous
    have heq : (Subtype.val : S → Affine n) ⁻¹' (W ∩ S) =
        Set.inclusion hST ⁻¹' ((Subtype.val : T → Affine n) ⁻¹' W) := by
      ext x
      simp only [mem_preimage, mem_inter_iff, x.property, and_true, Set.inclusion]
    rw [heq]
    exact hpre
  exact ⟨m,W ∩ S,inter_subset_right,hW',⟨hqW,hq⟩,D',hD',
    ⟨e.restrict inter_subset_left hD'D he⟩⟩

theorem relative_open_trans {X : Type*} [TopologicalSpace X] {S T W : Set X}
    (_hTS : T ⊆ S) (hWT : W ⊆ T)
    (hT : IsOpen ((Subtype.val : S → X) ⁻¹' T))
    (hW : IsOpen ((Subtype.val : T → X) ⁻¹' W)) :
    IsOpen ((Subtype.val : S → X) ⁻¹' W) := by
  obtain ⟨O,hO,he⟩ := isOpen_induced_iff.mp hW
  have heq : (Subtype.val : S → X) ⁻¹' W =
      ((Subtype.val : S → X) ⁻¹' T) ∩ ((Subtype.val : S → X) ⁻¹' O) := by
    ext x
    constructor
    · intro hx
      refine ⟨hWT hx,?_⟩
      have hmem : (⟨x.val,hWT hx⟩ : T) ∈ (Subtype.val : T → X) ⁻¹' W := hx
      rw [← he] at hmem
      exact hmem
    · intro hx
      have hmem : (⟨x.val,hx.1⟩ : T) ∈ (Subtype.val : T → X) ⁻¹' O := hx.2
      rw [he] at hmem
      exact hmem
  rw [heq]
  exact hT.inter (hO.preimage continuous_subtype_val)

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscCompactness
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
section IntrinsicCompactness
open Set Metric Filter
open scoped Topology Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


theorem open_discRelation_nhds [ProperSpace E] {S : Set E} (hS : IsOpen S)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : S) :
    ∀ᶠ y in 𝓝 x, DiscRelation S r x y := by
  obtain ⟨δ,hδ,K,_hK,hKS,hxK,hrel⟩ := open_small_disc_carrier hS x.property hr hr1
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  obtain ⟨hyK,hh⟩ := hrel y.val (show dist y.val x.val < δ from hy)
  exact hh.mono hKS

open scoped Pointwise

end IntrinsicCompactness

open Set

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuityPrinciple
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

theorem HolomorphicOnSubset.restrict {d n : ℕ} {S W : Set (Affine d)}
    {f : S → Affine n} (hf : HolomorphicOnSubset S f) (hWS : W ⊆ S) :
    HolomorphicOnSubset W (fun p => f ⟨p.val,hWS p.property⟩) := by
  intro p
  obtain ⟨O,hO,hpO,F,hF,he⟩ := hf ⟨p.val,hWS p.property⟩
  exact ⟨O,hO,hpO,F,hF,fun q hqO => he ⟨q.val,hWS q.property⟩ hqO⟩

open Filter
open scoped Topology

theorem RelationSteps.mono {X : Type*} {R : X → X → Prop} {m n : ℕ}
    (hmn : m ≤ n) {x y : X} (h : RelationSteps R m x y) : RelationSteps R n x y := by
  induction n,hmn using Nat.le_induction with
  | base => exact h
  | succ _ _ ih => exact Or.inl ih

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompactPeakRatio
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set
open Filter
open scoped Topology

theorem RelationSteps.trans {X : Type*} {R : X → X → Prop} {m n : ℕ} {x y z : X}
    (hxy : RelationSteps R m x y) (hyz : RelationSteps R n y z) :
    RelationSteps R (m+n) x z := by
  induction n generalizing z with
  | zero => exact hyz ▸ hxy
  | succ n ih =>
      rcases hyz with hyz | ⟨w,hyw,hwz⟩
      · exact Or.inl (ih hyz)
      · exact Or.inr ⟨w,ih hyw,hwz⟩

theorem RelationSteps.single {X : Type*} {R : X → X → Prop} {x y : X} (h : R x y) :
    RelationSteps R 1 x y := Or.inr ⟨x,rfl,h⟩

theorem compact_connected_relation_chains {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (R : X → X → Prop)
    (hsym : ∀ x y, R x y → R y x)
    (hloc : ∀ x, ∀ᶠ y in 𝓝 x, R x y)
    (x : X) {C : Set X} (hC : IsCompact C) :
    ∃ n : ℕ, ∀ y ∈ C, RelationSteps R n x y := by
  classical
  let P : X → X → Prop := fun a b => ∃ n, RelationSteps R n a b
  have htrans : IsTrans X P := ⟨fun _ _ _ h₁ h₂ => by
    obtain ⟨n,hn⟩ := h₁
    obtain ⟨m,hm⟩ := h₂
    exact ⟨n+m,hn.trans hm⟩⟩
  have hP : ∀ y, P x y := PreconnectedSpace.induction₂' P (fun a => by
    filter_upwards [hloc a] with b hb
    exact ⟨⟨1,RelationSteps.single hb⟩,⟨1,RelationSteps.single (hsym a b hb)⟩⟩) htrans x
  choose N hN using hP
  have hnhd : ∀ y, {z | RelationSteps R (N y + 1) x z} ∈ 𝓝 y := by
    intro y
    filter_upwards [hloc y] with z hz
    exact (hN y).trans (RelationSteps.single hz)
  obtain ⟨I,_,hI⟩ := hC.elim_nhds_subcover
    (fun y => {z | RelationSteps R (N y + 1) x z}) (fun y _ => hnhd y)
  refine ⟨I.sup (fun y => N y+1),?_⟩
  intro y hy
  obtain ⟨a,ha,hay⟩ := mem_iUnion₂.mp (hI hy)
  exact RelationSteps.mono (Finset.le_sup (f := fun y => N y+1) ha) hay

theorem IsSmooth.discRelation_nhds {n : ℕ} {U : Set (Affine n)} (hU : IsSmooth U)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x : U) :
    ∀ᶠ y in 𝓝 x, DiscRelation U r x y := by
  classical
  obtain ⟨d,W,hWU,hW,hxW,D,hD,⟨e⟩⟩ := hU x
  let xW : W := ⟨x.val,hxW⟩
  let f : U → W := fun y => if hy : y.val ∈ W then ⟨y.val,hy⟩ else xW
  have hfval : (fun y => (f y).val) =ᶠ[𝓝 x] (fun y : U => y.val) := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    change y.val ∈ W at hy
    simp [f,hy]
  have hfx : f x = xW := by simp [f,xW,hxW]
  have hfc : ContinuousAt f x := by
    apply (Topology.IsEmbedding.subtypeVal.isInducing.continuousAt_iff).mpr
    exact continuous_subtype_val.continuousAt.congr_of_eventuallyEq hfval
  have hec : Tendsto (fun y => e.toHomeomorph (f y)) (𝓝 x) (𝓝 (e.toHomeomorph xW)) := by
    simpa only [Function.comp_def,hfx] using e.toHomeomorph.continuous.continuousAt.tendsto.comp hfc.tendsto
  filter_upwards [hec (open_discRelation_nhds hD hr hr1 (e.toHomeomorph xW)),
    hW.mem_nhds hxW] with y hy hyW
  change y.val ∈ W at hyW
  have hback := hy.map e.holomorphic_invFun hr1
  simp only [Homeomorph.symm_apply_apply] at hback
  have hout := hback.mono hWU
  simpa only [f,dite_eq_left hyW,xW] using hout

theorem disc_peak_ratio {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1)
    {a b : ℂ} (ha : ‖a‖ < 1/8) (hb : ‖b‖ < 1/8) :
    ‖1-f b‖ ≤ 3*‖1-f a‖ := by
  have hmaps : MapsTo (fun z : ℂ => a+z) (ball 0 (1/2)) (ball 0 1) := by
    intro z hz
    rw [mem_ball,dist_zero_right] at hz ⊢
    exact (norm_add_le a z).trans_lt (by linarith)
  let g : ℂ → ℂ := fun z => f (a+z)-f a
  have hg : DifferentiableOn ℂ g (ball 0 (1/2)) :=
    (hf.comp (by fun_prop) hmaps).sub_const _
  have hba : ‖b-a‖ < 1/4 := (norm_sub_le b a).trans_lt (by linarith)
  have hz : b-a ∈ ball (0 : ℂ) (1/2) := by
    rw [mem_ball,dist_zero_right]; linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let M : ℝ := ‖1-f a‖ + ε/2
  have hM : 0 < M := by dsimp [M]; positivity
  have hgre : MapsTo g (ball 0 (1/2)) {z | z.re ≤ M} := by
    intro z hz
    have hRe : (f (a+z)).re ≤ 1 := (Complex.re_le_norm _).trans (hbound _ (hmaps hz))
    have hRea : 1 - (f a).re ≤ ‖1-f a‖ := by simpa using Complex.re_le_norm (1-f a)
    change (f (a+z)-f a).re ≤ M
    rw [Complex.sub_re]
    dsimp [M]
    linarith
  have hbc := Complex.borelCaratheodory_zero hM hg hgre (by norm_num) hz
    (by simp [g])
  have hden : 0 < 1/2-‖b-a‖ := by linarith
  have hbc' : ‖f b-f a‖ ≤ 2*M := by
    have htranslate : a + (b - a) = b := by ring
    simp only [g,htranslate] at hbc
    apply hbc.trans
    apply (div_le_iff₀ hden).mpr
    nlinarith
  calc
    ‖1-f b‖ ≤ ‖1-f a‖ + ‖f a-f b‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖1-f a‖ + 2*M := by rw [norm_sub_rev (f a) (f b)]; exact add_le_add (le_refl _) hbc'
    _ = 3*‖1-f a‖ + ε := by dsimp [M]; ring

theorem DiscRelation.entire_peak_ratio {n : ℕ} {U : Set (Affine n)}
    {g : Affine n → ℂ} (hg : Differentiable ℂ g)
    (hbound : ∀ z ∈ U, ‖g z‖ ≤ 1) {x y : U}
    (hxy : DiscRelation U (1/8) x y) :
    ‖1-g y.val‖ ≤ 3*‖1-g x.val‖ := by
  obtain ⟨f,hf,hU,a,b,ha,hb,hax,hby⟩ := hxy
  have he := disc_peak_ratio (hg.comp_differentiableOn hf) (fun z hz => hbound _ (hU hz)) ha hb
  simpa only [Function.comp_apply,hax,hby] using he

theorem RelationSteps.symm {X : Type*} {R : X → X → Prop}
    (hsym : ∀ x y, R x y → R y x) {j : ℕ} {x y : X}
    (h : RelationSteps R j x y) : RelationSteps R j y x := by
  induction j generalizing x y with
  | zero => exact Eq.symm h
  | succ j ih =>
      rcases h with h | ⟨z,hxz,hzy⟩
      · exact Or.inl (ih h)
      · simpa only [Nat.add_comm 1 j] using
          (RelationSteps.single (hsym z y hzy)).trans (ih hxz)

theorem RelationSteps.map {X Y : Type*} {R : X → X → Prop} {S : Y → Y → Prop}
    {f : X → Y} (hf : ∀ x y, R x y → S (f x) (f y)) {j : ℕ} {x y : X}
    (h : RelationSteps R j x y) : RelationSteps S j (f x) (f y) := by
  induction j generalizing y with
  | zero => exact congrArg f h
  | succ j ih =>
      rcases h with h | ⟨z,hxz,hzy⟩
      · exact Or.inl (ih h)
      · exact Or.inr ⟨f z,ih hxz,hf z y hzy⟩

theorem RelationSteps.ratio {X : Type*} {R : X → X → Prop} {v : X → ℝ}
    (hv : ∀ x, 0 ≤ v x) {c : ℝ} (hc : 1 ≤ c)
    (hR : ∀ x y, R x y → v y ≤ c*v x) {j : ℕ} {x y : X}
    (h : RelationSteps R j x y) : v y ≤ c^j*v x := by
  induction j generalizing y with
  | zero =>
      change x = y at h
      subst y
      simp
  | succ j ih =>
      have hc0 : 0 ≤ c := le_trans zero_le_one hc
      rcases h with h | ⟨z,hxz,hzy⟩
      · calc
          v y ≤ c^j*v x := ih h
          _ ≤ c^(j+1)*v x := mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hc (Nat.le_succ _)) (hv x)
      · calc
          v y ≤ c*v z := hR z y hzy
          _ ≤ c*(c^j*v x) := mul_le_mul_of_nonneg_left (ih hxz) hc0
          _ = c^(j+1)*v x := by rw [pow_succ]; ring

theorem IsSmooth.compact_disc_chains {n : ℕ} {U : Set (Affine n)}
    [Nonempty U] [PreconnectedSpace U] (hU : IsSmooth U)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {K E : Set U} (hK : IsCompact K) (hE : IsCompact E) :
    ∃ N : ℕ, ∀ k ∈ K, ∀ q ∈ E, RelationSteps (DiscRelation U r) N k q := by
  let x : U := Classical.choice inferInstance
  obtain ⟨N,hN⟩ := compact_connected_relation_chains (DiscRelation U r)
    (fun _ _ h => discRelation_symm h) (hU.discRelation_nhds hr hr1) x (hK.union hE)
  refine ⟨N+N,?_⟩
  intro k hk q hq
  exact ((hN k (Or.inl hk)).symm (fun _ _ h => discRelation_symm h)).trans
    (hN q (Or.inr hq))

theorem IsSmooth.compact_peak_ratio {n : ℕ} {U : Set (Affine n)}
    [Nonempty U] [PreconnectedSpace U] (hU : IsSmooth U)
    {K E : Set U} (hK : IsCompact K) (hE : IsCompact E) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Affine n → ℂ, Differentiable ℂ g →
      (∀ z ∈ U, ‖g z‖ ≤ 1) → ∀ f : U → U,
      HolomorphicOnSubset U (fun z => (f z).val) →
      ∀ k ∈ K, ∀ q ∈ E, ‖1-g (f q).val‖ ≤ C*‖1-g (f k).val‖ := by
  obtain ⟨N,hN⟩ := hU.compact_disc_chains (by norm_num : 0 < (1:ℝ)/8)
    (by norm_num : (1:ℝ)/8 ≤ 1) hK hE
  refine ⟨3^N,by positivity,?_⟩
  intro g hg hb f hf k hk q hq
  have hchain := (hN k hk q hq).map
    (fun _ _ h => h.map hf (by norm_num : (1:ℝ)/8 ≤ 1))
  exact hchain.ratio (fun _ => norm_nonneg _) (by norm_num : (1:ℝ) ≤ 3)
    (fun _ _ h => h.entire_peak_ratio hg hb)

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuousFderivLocallyUniform
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem approximatesLinearOn_of_fderiv_close {s : Set E} (hs : Convex ℝ s)
    {f : E → F} (L : E →L[ℂ] F) {c : ℝ≥0}
    (hf : ∀ x ∈ s, DifferentiableAt ℂ f x)
    (hd : ∀ x ∈ s, ‖fderiv ℂ f x-L‖ ≤ c) :
    ApproximatesLinearOn f L s c := by
  apply LipschitzOnWith.approximatesLinearOn
  apply hs.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
  · intro x hx
    exact (hf x hx).sub L.differentiableAt
  · intro x hx
    change ‖fderiv ℂ (fun y => f y-L y) x‖ ≤ (c : ℝ)
    simpa only [fderiv_fun_sub (hf x hx) L.differentiableAt,L.fderiv] using hd x hx

theorem stable_image_ball [CompleteSpace E] [Nontrivial F]
    {f : E → F} (L : E ≃L[ℂ] F) {x : E} {y : F} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall x R, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ closedBall x R,
      ‖fderiv ℂ f z-(L : E →L[ℂ] F)‖ ≤ ‖(L.symm : F →L[ℂ] E)‖⁻¹/2)
    (hc : dist y (f x) < ‖(L.symm : F →L[ℂ] E)‖⁻¹*R/4) :
    ball y (‖(L.symm : F →L[ℂ] E)‖⁻¹*R/4) ⊆ f '' closedBall x R := by
  let c : ℝ≥0 := ⟨‖(L.symm : F →L[ℂ] E)‖⁻¹/2, by positivity⟩
  have ha : ApproximatesLinearOn f (L : E →L[ℂ] F) (closedBall x R) c :=
    approximatesLinearOn_of_fderiv_close (c := c) (f := f)
      (convex_closedBall x R) (L : E →L[ℂ] F) hf hd
  have hsur := ha.surjOn_closedBall_of_nonlinearRightInverse L.toNonlinearRightInverse hR.le Subset.rfl
  intro z hz
  apply hsur
  change dist z (f x) ≤ (‖(L.symm : F →L[ℂ] E)‖⁻¹ -
    ‖(L.symm : F →L[ℂ] E)‖⁻¹/2)*R
  have hz' := mem_ball.mp hz
  have ht := dist_triangle z y (f x)
  linarith

theorem eventually_image_ball [CompleteSpace E] [ProperSpace E] [CompleteSpace F]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → F} {g : E → F}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W)
    {x : E} (hx : x ∈ S) (L : E ≃L[ℂ] F)
    (hL : fderiv ℂ g x = (L : E →L[ℂ] F))
    (hdg : ContinuousAt (fderiv ℂ g) x) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ S ∧
      ∀ᶠ j in atTop, ball (g x) r ⊆ f j '' closedBall x R := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
    refine ⟨1,by norm_num,R/2,half_pos hR,
      (closedBall_subset_ball (by linarith)).trans hsub,Filter.Eventually.of_forall ?_⟩
    intro j y hy
    exact ⟨x,mem_closedBall_self (by positivity),Subsingleton.elim _ _⟩
  let A : ℝ := ‖(L.symm : F →L[ℂ] E)‖⁻¹
  have hA : 0 < A := inv_pos.mpr L.symm.norm_pos
  have hnear : ∀ᶠ z in 𝓝 x, ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖ < A/4 := by
    have ht : Tendsto (fun z => ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖) (𝓝 x) (𝓝 0) := by
      simpa [hL] using (hdg.sub_const (L : E →L[ℂ] F)).norm
    exact (tendsto_order.mp ht).2 (A/4) (by positivity)
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hS.mem_nhds hx) (inter_mem hW hnear))
  have hbsub : ball x R ⊆ S := fun z hz => (hsub hz).1
  have hclsub : closedBall x (R/2) ⊆ ball x R := closedBall_subset_ball (by linarith)
  have hconv := tendstoLocallyUniformlyOn_fderiv hS hfg hf
  have hdunif : TendstoUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) atTop
      (closedBall x (R/2)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x (R/2))).mp (hconv.mono (hclsub.trans hbsub))
  have hcenter : ∀ᶠ j in atTop, dist (g x) (f j x) < A*(R/2)/4 := by
    have ht : Tendsto (fun j => dist (g x) (f j x)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x))).dist (hfg.tendsto_at hx)
    exact (tendsto_order.mp ht).2 _ (by positivity)
  refine ⟨A*(R/2)/4,by positivity,R/2,half_pos hR,hclsub.trans hbsub,?_⟩
  filter_upwards [hhol,hcenter,Metric.tendstoUniformlyOn_iff.mp hdunif (A/4) (by positivity)] with j hj hc hd
  apply stable_image_ball L (half_pos hR) ?_ ?_ hc
  · intro z hz
    exact (hj.mono (fun y hy => (hsub hy).2.1)).differentiableAt
      (isOpen_ball.mem_nhds (hclsub hz))
  · intro z hz
    have he : ‖fderiv ℂ (f j) z-fderiv ℂ g z‖ < A/4 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hd z hz
    have hn := (hsub (hclsub hz)).2.2
    change ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖ < A/4 at hn
    have ht : ‖fderiv ℂ (f j) z-(L : E →L[ℂ] F)‖ ≤
        ‖fderiv ℂ (f j) z-fderiv ℂ g z‖ + ‖fderiv ℂ g z-(L : E →L[ℂ] F)‖ := by
      simpa only [dist_eq_norm] using dist_triangle (fderiv ℂ (f j) z) (fderiv ℂ g z) (L : E →L[ℂ] F)
    change ‖fderiv ℂ (f j) z-(L : E →L[ℂ] F)‖ ≤ A/2
    linarith

end Release061



end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HurwitzZeroFreeOr
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061
open Set Filter Metric
open scoped Topology

theorem hurwitz_zero_interior {S : Set ℂ} (hS : IsOpen S)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) S)
    (hne : ∀ᶠ j in atTop, ∀ z ∈ S, f j z ≠ 0)
    {p : ℂ} (hp : p ∈ S) (hgp : g p = 0) :
    ∀ᶠ z in 𝓝 p, g z = 0 := by
  have hg := hfg.differentiableOn hf hS
  rcases (hg.analyticAt (hS.mem_nhds hp)).eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · exact hz
  exfalso
  have he : ∀ᶠ z in 𝓝 p, z ≠ p → g z ≠ 0 := by
    simpa only [mem_compl_iff,mem_singleton_iff] using eventually_nhdsWithin_iff.mp hn
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (he.and (hS.mem_nhds hp))
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hcl : closedBall p r ⊆ S := by
    intro z hz
    exact (hsub (closedBall_subset_ball (by dsimp [r]; linarith) hz)).2
  have hnsp : ∀ z ∈ sphere p r, g z ≠ 0 := by
    intro z hz
    apply (hsub (closedBall_subset_ball (by dsimp [r]; linarith) (sphere_subset_closedBall hz))).1
    intro hzp
    have hd := mem_sphere.mp hz
    rw [hzp,dist_self] at hd
    linarith
  obtain ⟨z₀,hz₀,hmin⟩ := (isCompact_sphere p r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    ((hg.continuousOn.mono (sphere_subset_closedBall.trans hcl)).norm)
  let δ := ‖g z₀‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hnsp z₀ hz₀)
  have hunif : TendstoUniformlyOn f g atTop (sphere p r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_sphere p r)).mp (hfg.mono (sphere_subset_closedBall.trans hcl))
  have hsmall : ∀ᶠ j in atTop, ‖f j p‖ < δ/2 := by
    have ht : Tendsto (fun j => ‖f j p‖) atTop (𝓝 0) := by
      simpa [hgp] using (hfg.tendsto_at hp).norm
    exact (tendsto_order.mp ht).2 (δ/2) (half_pos hδ)
  have hcontr : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hf,hne,hsmall,Metric.tendstoUniformlyOn_iff.mp hunif (δ/2) (half_pos hδ)] with j hj hjne hjs hju
    have hinv : DiffContOnCl ℂ (fun z => (f j z)⁻¹) (ball p r) :=
      DiffContOnCl.mk_ball ((hj.inv hjne).mono (ball_subset_closedBall.trans hcl))
        ((hj.continuousOn.inv₀ hjne).mono hcl)
    have hbound : ∀ z ∈ frontier (ball p r), ‖(f j z)⁻¹‖ ≤ (δ/2)⁻¹ := by
      intro z hz
      rw [frontier_ball p hr.ne'] at hz
      have htri := norm_le_norm_sub_add (g z) (f j z)
      have herr : ‖g z-f j z‖ < δ/2 := by simpa only [dist_eq_norm] using hju z hz
      have hm : δ ≤ ‖g z‖ := hmin hz
      have hlo : δ/2 ≤ ‖f j z‖ := by linarith
      rw [norm_inv]
      exact inv_anti₀ (half_pos hδ) hlo
    have hcenter := Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball : Bornology.IsBounded (ball p r)) hinv hbound
      (subset_closure (mem_ball_self hr))
    rw [norm_inv] at hcenter
    have hlo : δ/2 ≤ ‖f j p‖ := (inv_le_inv₀ (norm_pos_iff.mpr (hjne p hp)) (half_pos hδ)).mp hcenter
    linarith
  exact (Filter.Eventually.exists hcontr).choose_spec

theorem hurwitz_zero_interior_finiteDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → ℂ} {g : E → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) S)
    (hne : ∀ᶠ j in atTop, ∀ z ∈ S, f j z ≠ 0)
    {p : E} (hp : p ∈ S) (hgp : g p = 0) :
    ∀ᶠ z in 𝓝 p, g z = 0 := by
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hp)
  filter_upwards [ball_mem_nhds p (half_pos hR)] with y hy
  let l : ℂ → E := fun z => p+z • (y-p)
  have hl : Differentiable ℂ l := by
    intro z
    exact (differentiableAt_const p).add (differentiableAt_id.smul_const _)
  have hm : MapsTo l (ball 0 2) S := by
    intro z hz
    apply hsub
    rw [mem_ball,dist_eq_norm]
    have hy' : ‖y-p‖ < R/2 := by simpa only [mem_ball,dist_eq_norm] using hy
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    simp only [l,add_sub_cancel_left,norm_smul]
    nlinarith [norm_nonneg z,norm_nonneg (y-p)]
  have hconv := hfg.comp l hm hl.continuous.continuousOn
  have hdiff : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j ∘ l) (ball 0 2) :=
    hf.mono fun j hj => hj.comp hl.differentiableOn hm
  have hnonzero : ∀ᶠ j in atTop, ∀ z ∈ ball 0 2, (f j ∘ l) z ≠ 0 :=
    hne.mono fun j hj z hz => hj (l z) (hm hz)
  have h0 : (g ∘ l) 0 = 0 := by simpa [l] using hgp
  have he := hurwitz_zero_interior isOpen_ball hconv hdiff hnonzero
    (mem_ball_self (by norm_num : (0:ℝ)<2)) h0
  have hg := (hconv.differentiableOn hdiff isOpen_ball).analyticOnNhd isOpen_ball
  have hall := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0:ℂ) 2).isPreconnected (mem_ball_self (by norm_num)) he
  have h1 := hall (by norm_num : (1:ℂ) ∈ ball 0 2)
  simpa [l,Function.comp_def] using h1

end Release061



end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EventuallyImageBallNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_montel_expanding_domains {n m : ℕ} {S : Set (Affine n)}
    (hS : IsOpen S) (f : ℕ → Affine n → Affine m)
    (hlocal : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ball x r ⊆ S ∧ ∀ᶠ j in atTop,
        DifferentiableOn ℂ (f j) (ball x r) ∧ ∀ y ∈ ball x r, ‖f j y‖ ≤ M) :
    ∃ g : Affine n → Affine m, AnalyticOnNhd ℂ g S ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j => f (φ j)) g atTop S := by
  obtain ⟨g,hg,φ,hφ,hconv⟩ := montel_expanding_domains hS f hlocal
  exact ⟨g,analyticOnNhd_of_differentiableOn_affine hS hg,φ,hφ,hconv⟩

theorem analyticAt_clm_det {n : ℕ}
    (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
    AnalyticAt ℂ (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T.det) L := by
  classical
  have he : ∀ i j : Fin n, AnalyticAt ℂ
      (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T (Pi.single j 1) i) L := by
    intro i j
    exact ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℂ (Fin n → ℂ) (Pi.single j 1))).analyticAt L
  have hd : (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T.det) =
      fun T => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ i, T (Pi.single i 1) (σ i) := by
    funext T
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' T.toLinearMap, Matrix.det_apply']
    rfl
  rw [hd]
  have hs := Finset.analyticAt_sum Finset.univ (fun σ _ =>
    (show AnalyticAt ℂ (fun _ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => (Equiv.Perm.sign σ : ℂ)) L from analyticAt_const).mul
      (Finset.analyticAt_prod Finset.univ (fun i _ => he (σ i) i)))
  simpa only [Finset.sum_fn,Finset.prod_fn,Pi.mul_apply] using hs

theorem analyticOnNhd_jacobian {n : ℕ} {S : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → (Fin n → ℂ)} (hf : AnalyticOnNhd ℂ f S) :
    AnalyticOnNhd ℂ (fun x => (fderiv ℂ f x).det) S := by
  intro x hx
  exact (analyticAt_clm_det (fderiv ℂ f x)).comp (hf x hx).fderiv

theorem tendstoLocallyUniformlyOn_jacobian {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : ℕ → (Fin n → ℂ) → (Fin n → ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W) :
    TendstoLocallyUniformlyOn (fun j x => (fderiv ℂ (f j) x).det)
      (fun x => (fderiv ℂ g x).det) atTop S := by
  have hg := analyticOnNhd_of_differentiableOn_affine hS
    (differentiableOn_of_locally_uniform_limit hS hfg hf)
  exact locallyUniform_postcomp (tendstoLocallyUniformlyOn_fderiv hS hfg hf)
    hg.fderiv.continuousOn ContinuousLinearMap.continuous_det

theorem hurwitz_zero_free_or_zero_locally
    {n : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hconn : IsPreconnected S)
    {f : ℕ → (Fin n → ℂ) → ℂ} {g : (Fin n → ℂ) → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (f j) W ∧ ∀ z ∈ W, f j z ≠ 0) :
    (∀ z ∈ S, g z ≠ 0) ∨ (∀ z ∈ S, g z = 0) := by
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hf x hx
    exact ⟨W,hW,he.mono fun _ h => h.1⟩
  have hc := (differentiableOn_of_locally_uniform_limit hS hfg hdiff).continuousOn
  have hzero : ∀ p ∈ S, g p = 0 → ∀ᶠ z in 𝓝 p, g z = 0 := by
    intro p hp hgp
    obtain ⟨W,hW,he⟩ := hf p hp
    obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hp))
    exact hurwitz_zero_interior_finiteDim isOpen_ball
      (hfg.mono fun z hz => (hsub hz).2)
      (he.mono fun _ h => h.1.mono fun z hz => (hsub hz).1)
      (he.mono fun _ h z hz => h.2 z (hsub hz).1) (mem_ball_self hR) hgp
  by_cases hn : ∀ z ∈ S, g z ≠ 0
  · exact Or.inl hn
  right
  push Not at hn
  obtain ⟨p,hp,hgp⟩ := hn
  let Z := {z | z ∈ S ∧ g z = 0}
  let N := {z | z ∈ S ∧ g z ≠ 0}
  have hZ : IsOpen Z := isOpen_iff_mem_nhds.mpr fun z hz =>
    inter_mem (hS.mem_nhds hz.1) (hzero z hz.1 hz.2)
  have hN : IsOpen N := isOpen_iff_mem_nhds.mpr fun z hz =>
    inter_mem (hS.mem_nhds hz.1)
      (((hc z hz.1).continuousAt (hS.mem_nhds hz.1)).eventually_ne hz.2)
  have hdis : Disjoint Z N := Set.disjoint_left.mpr fun _ hz hn => hn.2 hz.2
  have hcover : S ⊆ Z ∪ N := by
    intro z hz
    by_cases hg : g z = 0
    · exact Or.inl ⟨hz,hg⟩
    · exact Or.inr ⟨hz,hg⟩
  have hsub := hconn.subset_left_of_subset_union hZ hN hdis hcover ⟨p,hp,hp,hgp⟩
  exact fun z hz => (hsub hz).2

theorem jacobian_nonzero_of_anchor {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) (hconn : IsPreconnected S)
    {f : ℕ → (Fin n → ℂ) → (Fin n → ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j) W ∧ ∀ z ∈ W, (fderiv ℂ (f j) z).det ≠ 0)
    (hanchor : ∃ p ∈ S, (fderiv ℂ g p).det ≠ 0) :
    ∀ p ∈ S, (fderiv ℂ g p).det ≠ 0 := by
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hf x hx
    exact ⟨W,hW,he.mono fun _ h => h.1.differentiableOn⟩
  have hconv := tendstoLocallyUniformlyOn_jacobian hS hfg hdiff
  have hlocal : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (fun z => (fderiv ℂ (f j) z).det) W ∧
        ∀ z ∈ W, (fderiv ℂ (f j) z).det ≠ 0 := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hf x hx
    exact ⟨W,hW,he.mono fun _ h => ⟨(analyticOnNhd_jacobian h.1).differentiableOn,h.2⟩⟩
  rcases hurwitz_zero_free_or_zero_locally hS hconn hconv hlocal with h | h
  · exact h
  · obtain ⟨p,hp,hpne⟩ := hanchor
    exact (hpne (h p hp)).elim

theorem eventually_image_ball_of_nonzero_jacobian {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : ℕ → (Fin n → ℂ) → (Fin n → ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j) W)
    {x : Fin n → ℂ} (hx : x ∈ S) (hne : (fderiv ℂ g x).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ S ∧
      ∀ᶠ j in atTop, ball (g x) r ⊆ f j '' closedBall x R := by
  let L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ g x).toLinearMap hne).toContinuousLinearEquiv
  have hL : fderiv ℂ g x = (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) := by
    ext v i
    rfl
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro z hz
    obtain ⟨W,hW,he⟩ := hf z hz
    exact ⟨W,hW,he.mono fun _ h => h.differentiableOn⟩
  exact eventually_image_ball hS hfg hdiff hx L hL
    (continuousAt_fderiv_of_locally_uniform_analytic hS hfg hf hx)

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HomeomorphInverse
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem mapsTo_of_stable_balls_and_excluded_points
    {X Y : Type*} [PseudoMetricSpace Y] {S : Set X} {O : Set Y}
    {T : ℕ → Set Y} {f : X → Y}
    (hstable : ∀ x ∈ S, ∃ r > 0, ∀ᶠ j in atTop, ball (f x) r ⊆ T j)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Y,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j) : MapsTo f S O := by
  intro x hx
  by_contra hout
  obtain ⟨r,hr,hball⟩ := hstable x hx
  obtain ⟨a,ha,houta⟩ := hexcluded (f x) hout
  have hnear : ∀ᶠ j in atTop, a j ∈ ball (f x) r := ha (ball_mem_nhds _ hr)
  have hfalse : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hball,houta,hnear] with j hj ho hn
    exact ho (hj hn)
  exact (Filter.Eventually.exists hfalse).choose_spec

end Release061



end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalingOpenDomain
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem holomorphicOnSubset_of_analyticOnNhd_open {n m : ℕ}
    {S : Set (Affine n)} (hS : IsOpen S) {f : Affine n → Affine m}
    (hf : AnalyticOnNhd ℂ f S) : HolomorphicOnSubset S (fun x => f x) := by
  intro p
  exact ⟨S,hS,p.property,f,hf,fun _ _ => rfl⟩

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicLocallyUniformLimit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

lemma continuousOn_ambientExtend {n m : ℕ} {S : Set (Affine n)}
    {f : S → Affine m} (hf : Continuous f) : ContinuousOn (ambientExtend f) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : S.domRestrict (ambientExtend f) = f := funext (ambientExtend_apply f)
  rwa [he]

theorem holomorphicOnSubset_of_local {n m : ℕ} {S : Set (Affine n)}
    {f : S → Affine m}
    (hf : ∀ p : S, ∃ (W : Set (Affine n)) (hWS : W ⊆ S),
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      HolomorphicOnSubset W (fun x => f ⟨x.val,hWS x.property⟩)) :
    HolomorphicOnSubset S f := by
  intro p
  obtain ⟨W,hWS,hW,hpW,hh⟩ := hf p
  obtain ⟨O,hO,heO⟩ := isOpen_induced_iff.mp hW
  have hpO : p.val ∈ O := by change p ∈ (Subtype.val : S → Affine n) ⁻¹' O; rw [heO]; exact hpW
  obtain ⟨V,hV,hpV,F,hF,he⟩ := hh ⟨p.val,hpW⟩
  refine ⟨V ∩ O,hV.inter hO,⟨hpV,hpO⟩,F,hF.mono inter_subset_left,?_⟩
  intro q hq
  have hqW : q.val ∈ W := by
    change q ∈ (Subtype.val : S → Affine n) ⁻¹' W
    rw [← heO]
    exact hq.2
  exact he ⟨q.val,hqW⟩ hq.1

theorem holomorphic_chart_limit {n d m : ℕ} {W : Set (Affine n)}
    {D : Set (Affine d)} (hD : IsOpen D) (e : Biholomorph W D)
    {f : ℕ → Affine n → Affine m} {F : Affine n → Affine m}
    (hconv : TendstoLocallyUniformlyOn f F atTop W)
    (hhol : ∀ᶠ j in atTop, HolomorphicOnSubset W (fun x => f j x)) :
    HolomorphicOnSubset W (fun x => F x) := by
  let g : Affine d → Affine n := ambientExtend (fun x => (e.toHomeomorph.symm x).val)
  have hg : ∀ x : D, g x = (e.toHomeomorph.symm x).val :=
    ambientExtend_apply _
  have hgc : ContinuousOn g D := continuousOn_ambientExtend
    (continuous_subtype_val.comp e.toHomeomorph.symm.continuous)
  have hgm : MapsTo g D W := by
    intro y hy
    rw [hg ⟨y,hy⟩]
    exact (e.toHomeomorph.symm ⟨y,hy⟩).property
  have hc := hconv.comp g hgm hgc
  have hjhol : ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j ∘ g) D := by
    filter_upwards [hhol] with j hj
    have hh := (hj.comp e.holomorphic_invFun).analyticOnNhd_extend hD
    intro x hx
    apply (hh x hx).congr
    filter_upwards [hD.mem_nhds hx] with y hy
    simp only [Function.comp_def]
    rw [hg ⟨y,hy⟩]
    exact ambientExtend_apply _ ⟨y,hy⟩
  have hFd := differentiableOn_of_locally_uniform_limit hD hc
    (fun x hx => ⟨D,hD.mem_nhds hx,hjhol.mono fun _ h => h.differentiableOn⟩)
  have hFa := analyticOnNhd_of_differentiableOn_affine hD hFd
  have hlocal : HolomorphicOnSubset D (fun x => F (g x)) :=
    holomorphicOnSubset_of_analyticOnNhd_open hD hFa
  have hcomp := hlocal.comp e.holomorphic_toFun
  convert hcomp using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  dsimp only [Function.comp_def]
  rw [hg (e.toHomeomorph x),e.toHomeomorph.symm_apply_apply]

theorem IsSmooth.holomorphic_locally_uniform_limit {n m : ℕ} {S : Set (Affine n)}
    (hS : IsSmooth S) {f : ℕ → Affine n → Affine m} {F : Affine n → Affine m}
    (hconv : TendstoLocallyUniformlyOn f F atTop S)
    (hhol : ∀ p : S, ∃ V : Set (Affine n), V ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' V) ∧ p.val ∈ V ∧
      ∀ᶠ j in atTop, HolomorphicOnSubset V (fun x => f j x)) :
    HolomorphicOnSubset S (fun x => F x) := by
  apply holomorphicOnSubset_of_local
  intro p
  obtain ⟨V,hVS,hVo,hpV,hVhol⟩ := hhol p
  have hsm : SmoothAtSubset V p.val :=
    smoothAtSubset_restrict_open hVS hVo hpV (hS p)
  obtain ⟨d,W,hWV,hWo,hpW,D,hD,⟨e⟩⟩ := hsm
  refine ⟨W,hWV.trans hVS,relative_open_trans hVS hWV hVo hWo,hpW,?_⟩
  exact holomorphic_chart_limit hD e (hconv.mono (hWV.trans hVS))
    (hVhol.mono fun _ hj => hj.restrict hWV)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EventualEquicontinuityOpenSubset
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_comp_chart_inverse {n d m : ℕ} {W : Set (Affine n)}
    {D : Set (Affine d)} (hD : IsOpen D) (e : Biholomorph W D)
    {f : Affine n → Affine m} (hf : HolomorphicOnSubset W (fun x => f x)) :
    AnalyticOnNhd ℂ (f ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) D := by
  have hh := (hf.comp e.holomorphic_invFun).analyticOnNhd_extend hD
  intro x hx
  apply (hh x hx).congr
  filter_upwards [hD.mem_nhds hx] with y hy
  simp only [Function.comp_def,ambientExtend,dite_eq_left hy]

theorem chart_eventual_equicontinuity {n d m : ℕ} {W : Set (Affine n)}
    {D : Set (Affine d)} (hD : IsOpen D) (e : Biholomorph W D)
    {f : ℕ → Affine n → Affine m} {M : ℝ}
    (hf : ∀ᶠ j in atTop, HolomorphicOnSubset W (fun x => f j x) ∧
      ∀ y ∈ W, ‖f j y‖ ≤ M) (p : W) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set W, A ∈ 𝓝 p ∧ ∀ᶠ j in atTop,
      ∀ q ∈ A, dist (f j q.val) (f j p.val) < ε := by
  let z : Affine d := (e.toHomeomorph p).val
  obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds (e.toHomeomorph p).property)
  let A : Set W := {q | (e.toHomeomorph q).val ∈ ball z r ∧
      (2*M/r)*dist (e.toHomeomorph q).val z < ε}
  have hcc : Continuous (fun q : W => (e.toHomeomorph q).val) :=
    continuous_subtype_val.comp e.toHomeomorph.continuous
  have hA : A ∈ 𝓝 p := by
    have hball : ∀ᶠ q : W in 𝓝 p, (e.toHomeomorph q).val ∈ ball z r :=
      hcc.continuousAt.preimage_mem_nhds (ball_mem_nhds z hr)
    have hsmall : ∀ᶠ q : W in 𝓝 p, (2*M/r)*dist (e.toHomeomorph q).val z < ε := by
      have ht : Tendsto (fun q : W => (2*M/r)*dist (e.toHomeomorph q).val z)
          (𝓝 p) (𝓝 0) := by
        simpa only [z,dist_self,mul_zero] using (hcc.dist (continuous_const : Continuous (fun _ : W => z))).const_mul (2*M/r) |>.tendsto p
      exact (tendsto_order.mp ht).2 ε hε
    exact hball.and hsmall
  refine ⟨A,hA,?_⟩
  filter_upwards [hf] with j hj q hq
  let g := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
  have hg : ∀ x : D, g x = (e.toHomeomorph.symm x).val := ambientExtend_apply _
  have hgz : g z = p.val := by rw [hg (e.toHomeomorph p),e.toHomeomorph.symm_apply_apply]
  have hgq : g (e.toHomeomorph q).val = q.val := by
    rw [hg (e.toHomeomorph q),e.toHomeomorph.symm_apply_apply]
  have hbound : ∀ x ∈ ball z r, ‖f j (g x)‖ ≤ M := by
    intro x hx
    rw [hg ⟨x,hrD hx⟩]
    exact hj.2 _ (e.toHomeomorph.symm ⟨x,hrD hx⟩).property
  have hmap : MapsTo (f j ∘ g) (ball z r)
      (closedBall ((f j ∘ g) z) (2*M)) := by
    intro x hx
    rw [mem_closedBall,dist_eq_norm]
    dsimp only [Function.comp_def]
    exact (norm_sub_le _ _).trans (by linarith [hbound x hx,hbound z (mem_ball_self hr)])
  have hb := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((analytic_comp_chart_inverse hD e hj.1).differentiableOn.mono hrD) hmap hq.1
  change dist (f j (g (e.toHomeomorph q).val)) (f j (g z)) ≤ _ at hb
  rw [hgq,hgz] at hb
  exact hb.trans_lt hq.2

theorem eventual_equicontinuity_of_open_subset {X Y : Type*}
    [TopologicalSpace X] [PseudoMetricSpace Y] {S V : Set X}
    (hVS : V ⊆ S) (hV : IsOpen ((Subtype.val : S → X) ⁻¹' V))
    {p : X} (hpV : p ∈ V) {f : ℕ → X → Y} {ε : ℝ}
    (h : ∃ A : Set V, A ∈ 𝓝 (⟨p,hpV⟩ : V) ∧
      ∀ᶠ j in atTop, ∀ q ∈ A, dist (f j q.val) (f j p) < ε) :
    ∃ A : Set S, A ∈ 𝓝 (⟨p,hVS hpV⟩ : S) ∧
      ∀ᶠ j in atTop, ∀ q ∈ A, dist (f j q.val) (f j p) < ε := by
  obtain ⟨A,hA,he⟩ := h
  refine ⟨Set.inclusion hVS '' A,?_,?_⟩
  · have hi := Topology.IsOpenEmbedding.inclusion hVS hV
    rw [← hi.map_nhds_eq ⟨p,hpV⟩]
    exact Filter.image_mem_map hA
  · filter_upwards [he] with j hj q hq
    obtain ⟨v,hv,rfl⟩ := hq
    exact hj v hv

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartJacobianNeZero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem IsSmooth.montel_expanding {n m : ℕ} {S : Set (Affine n)}
    (hS : IsSmooth S) (f : ℕ → Affine n → Affine m)
    (hlocal : ∀ p : S, ∃ V : Set (Affine n), V ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' V) ∧ p.val ∈ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop,
        HolomorphicOnSubset V (fun x => f j x) ∧ ∀ y ∈ V, ‖f j y‖ ≤ M) :
    ∃ g : Affine n → Affine m, HolomorphicOnSubset S (fun x => g x) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun j => f (φ j)) g atTop S := by
  classical
  have hequi : ∀ p : S, ∀ ε, 0 < ε → ∃ A : Set S, A ∈ 𝓝 p ∧
      ∀ᶠ j in atTop, ∀ q ∈ A, dist (f j q.val) (f j p.val) < ε := by
    intro p ε hε
    obtain ⟨V,hVS,hVo,hpV,M,_,he⟩ := hlocal p
    obtain ⟨d,W,hWV,hWo,hpW,D,hD,⟨e⟩⟩ :=
      smoothAtSubset_restrict_open hVS hVo hpV (hS p)
    apply eventual_equicontinuity_of_open_subset (hWV.trans hVS)
      (relative_open_trans hVS hWV hVo hWo) hpW
    apply chart_eventual_equicontinuity (M := M) hD e _ (⟨p.val,hpW⟩ : W) hε
    exact he.mono fun j hj => ⟨hj.1.restrict hWV,fun y hy => hj.2 y (hWV hy)⟩
  have hcompact : ∀ p : S, ∃ K : Set (Affine m), IsCompact K ∧
      ∀ j, f j p.val ∈ K := by
    intro p
    obtain ⟨V,_,_,hpV,M,hM,he⟩ := hlocal p
    exact compact_range_of_eventually_norm_le hM (he.mono fun j hj => hj.2 p.val hpV)
  obtain ⟨g,_,φ,hφ,hconv⟩ :=
    locally_uniform_subsequence_of_eventual_equicontinuity
      (fun j (p : S) => f j p.val) hequi hcompact
  let G := ambientExtend g
  have hc : TendstoLocallyUniformlyOn (fun j => f (φ j)) G atTop S := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [Function.comp_def,G,ambientExtend,dite_eq_left (Subtype.prop _)] using hconv
  refine ⟨G,?_,φ,hφ,hc⟩
  apply hS.holomorphic_locally_uniform_limit hc
  intro p
  obtain ⟨V,hVS,hVo,hpV,M,hM,he⟩ := hlocal p
  exact ⟨V,hVS,hVo,hpV,hφ.tendsto_atTop (he.mono fun j hj => hj.1)⟩

theorem chart_jacobian_ne_zero_of_left_inverse {n m : ℕ}
    {W : Set (Affine n)} {D O : Set (Affine m)}
    (hD : IsOpen D) (hO : IsOpen O) (e : Biholomorph W D)
    {F : Affine n → Affine m} {G : Affine m → Affine n}
    (hF : HolomorphicOnSubset W (fun x => F x))
    (hG : AnalyticOnNhd ℂ G O)
    (hleft : ∀ q ∈ W, F q ∈ O → G (F q) = q)
    (q : W) (hqO : F q.val ∈ O) :
    (fderiv ℂ (F ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val))
      (e.toHomeomorph q).val).det ≠ 0 := by
  let z := (e.toHomeomorph q).val
  let E := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
  let H := F ∘ E
  have hz : z ∈ D := (e.toHomeomorph q).property
  have hEq : E z = q.val := by
    dsimp only [E,z]
    rw [ambientExtend_apply _ (e.toHomeomorph q),e.toHomeomorph.symm_apply_apply]
  have hHz : H z = F q.val := congrArg F hEq
  have hHa : AnalyticAt ℂ H z := analytic_comp_chart_inverse hD e hF z hz
  have hEa : AnalyticAt ℂ E z :=
    e.holomorphic_invFun.analyticOnNhd_extend hD z hz
  obtain ⟨A,hAo,hqA,φ,hφ,hext⟩ := e.holomorphic_toFun q
  have hφa : AnalyticAt ℂ φ (G (H z)) := by
    rw [hHz,hleft q q.property hqO]
    exact hφ q.val hqA
  have hGa : AnalyticAt ℂ G (H z) := by rw [hHz]; exact hG _ hqO
  have hideq : (φ ∘ G ∘ H) =ᶠ[𝓝 z] id := by
    have hEA : ∀ᶠ x in 𝓝 z, E x ∈ A := by
      apply hEa.continuousAt.preimage_mem_nhds
      rw [hEq]
      exact hAo.mem_nhds hqA
    have hHO : ∀ᶠ x in 𝓝 z, H x ∈ O := by
      apply hHa.continuousAt.preimage_mem_nhds
      rw [hHz]
      exact hO.mem_nhds hqO
    filter_upwards [hD.mem_nhds hz,hEA,hHO] with x hx hxA hxO
    have hEx : E x = (e.toHomeomorph.symm ⟨x,hx⟩).val := ambientExtend_apply _ ⟨x,hx⟩
    have hEW : E x ∈ W := hEx ▸ (e.toHomeomorph.symm ⟨x,hx⟩).property
    change φ (G (F (E x))) = x
    rw [hleft (E x) hEW hxO]
    rw [hEx] at hxA ⊢
    rw [hext (e.toHomeomorph.symm ⟨x,hx⟩) hxA]
    exact congrArg Subtype.val (e.toHomeomorph.apply_symm_apply ⟨x,hx⟩)
  have hd := ((hφa.differentiableAt.hasFDerivAt.comp (H z)
      hGa.differentiableAt.hasFDerivAt).comp z hHa.differentiableAt.hasFDerivAt).unique
      ((hasFDerivAt_id z).congr_of_eventuallyEq hideq)
  have hdet := congrArg ContinuousLinearMap.det hd
  change LinearMap.det
      (((fderiv ℂ φ (G (H z))).toLinearMap.comp (fderiv ℂ G (H z)).toLinearMap).comp
        (fderiv ℂ H z).toLinearMap) = LinearMap.det (LinearMap.id : Affine m →ₗ[ℂ] Affine m) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  intro hzero
  change LinearMap.det (fderiv ℂ H z).toLinearMap = 0 at hzero
  rw [hzero,mul_zero] at hdet
  exact zero_ne_one hdet

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartLimitMapsAnchor
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem chart_limit_mapsTo_of_anchor {n m : ℕ}
    {S W : Set (Affine n)} {D O : Set (Affine m)}
    (hWS : W ⊆ S) (hD : IsOpen D) (hconn : IsPreconnected D)
    (e : Biholomorph W D)
    {f : ℕ → Affine n → Affine m} {F : Affine n → Affine m}
    {T : ℕ → Set (Affine m)}
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hchart : ∀ᶠ j in atTop,
      HolomorphicOnSubset W (fun x => f j x) ∧
      ∀ z ∈ D, (fderiv ℂ
        (f j ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0)
    (hfmap : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, MapsTo (f j) K (T j))
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j)
    (hanchor : ∃ z ∈ D,
      (fderiv ℂ (F ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0) :
    MapsTo F W O := by
  let E := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
  have hEc : ContinuousOn E D := continuousOn_ambientExtend
    (continuous_subtype_val.comp e.toHomeomorph.symm.continuous)
  have hEm : MapsTo E D W := by
    intro x hx
    rw [show E x = (e.toHomeomorph.symm ⟨x,hx⟩).val from ambientExtend_apply _ ⟨x,hx⟩]
    exact (e.toHomeomorph.symm ⟨x,hx⟩).property
  have hconv := (hf.mono hWS).comp E hEm hEc
  have hhol : ∀ x ∈ D, ∃ A ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j ∘ E) A ∧ ∀ z ∈ A, (fderiv ℂ (f j ∘ E) z).det ≠ 0 := by
    intro x hx
    exact ⟨D,hD.mem_nhds hx,hchart.mono fun j hj =>
      ⟨analytic_comp_chart_inverse hD e hj.1,hj.2⟩⟩
  have hfull := jacobian_nonzero_of_anchor hD hconn hconv hhol hanchor
  have hhol' : ∀ x ∈ D, ∃ A ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j ∘ E) A := by
    intro x hx
    obtain ⟨A,hA,he⟩ := hhol x hx
    exact ⟨A,hA,he.mono fun j hj => hj.1⟩
  have hstable : ∀ x ∈ D, ∃ r > 0, ∀ᶠ j in atTop,
      ball ((F ∘ E) x) r ⊆ T j := by
    intro x hx
    obtain ⟨r,hr,R,_,hRD,he⟩ :=
      eventually_image_ball_of_nonzero_jacobian hD hconv hhol' hx (hfull x hx)
    have hK : IsCompact (E '' closedBall x R) :=
      (isCompact_closedBall x R).image_of_continuousOn (hEc.mono hRD)
    have hKS : E '' closedBall x R ⊆ S := by
      rintro y ⟨z,hz,rfl⟩
      exact hWS (hEm (hRD hz))
    refine ⟨r,hr,?_⟩
    filter_upwards [he,hfmap _ hK hKS] with j hj hm y hy
    obtain ⟨z,hz,hz'⟩ := hj hy
    exact hz' ▸ hm ⟨z,hz,rfl⟩
  have hmap := mapsTo_of_stable_balls_and_excluded_points hstable hexcluded
  intro q hq
  have hqE : E (e.toHomeomorph ⟨q,hq⟩).val = q := by
    dsimp only [E]
    rw [ambientExtend_apply _ (e.toHomeomorph ⟨q,hq⟩),e.toHomeomorph.symm_apply_apply]
  simpa only [Function.comp_def,hqE] using hmap (e.toHomeomorph ⟨q,hq⟩).property

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ExpandingBiholomorphismsCharts
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem chart_jacobian_of_biholomorph {n m : ℕ}
    {W S : Set (Affine n)} {D T : Set (Affine m)}
    (hWS : W ⊆ S) (hD : IsOpen D) (hT : IsOpen T)
    (e : Biholomorph W D) (b : Biholomorph S T)
    {f : Affine n → Affine m}
    (hf : ∀ q : W, f q.val = (b.toHomeomorph ⟨q.val,hWS q.property⟩).val) :
    HolomorphicOnSubset W (fun q => f q) ∧
      ∀ z ∈ D, (fderiv ℂ
        (f ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0 := by
  have hfh : HolomorphicOnSubset W (fun q => f q) := by
    intro q
    obtain ⟨A,hAo,hqA,φ,hφ,hext⟩ := b.holomorphic_toFun ⟨q.val,hWS q.property⟩
    refine ⟨A,hAo,hqA,φ,hφ,?_⟩
    intro r hr
    change φ r.val = f r.val
    rw [hf r]
    exact hext ⟨r.val,hWS r.property⟩ hr
  refine ⟨hfh,?_⟩
  intro z hz
  let G := ambientExtend (fun x : T => (b.toHomeomorph.symm x).val)
  have hGa : AnalyticOnNhd ℂ G T := b.holomorphic_invFun.analyticOnNhd_extend hT
  have hleft : ∀ q ∈ W, f q ∈ T → G (f q) = q := by
    intro q hq _
    rw [hf ⟨q,hq⟩]
    dsimp only [G]
    rw [ambientExtend_apply _ (b.toHomeomorph ⟨q,hWS hq⟩),b.toHomeomorph.symm_apply_apply]
  let q : W := e.toHomeomorph.symm ⟨z,hz⟩
  have hqT : f q.val ∈ T := by rw [hf q]; exact (b.toHomeomorph ⟨q.val,hWS q.property⟩).property
  have hn := chart_jacobian_ne_zero_of_left_inverse hD hT e hfh hGa hleft q hqT
  simpa only [q,e.toHomeomorph.apply_symm_apply] using hn

theorem expanding_biholomorphisms_charts {n m : ℕ} {S : Set (Affine n)}
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAS : ∀ j, A j ⊆ S)
    (hAo : ∀ j, IsOpen ((Subtype.val : S → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m)
    (hf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hcover : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, K ⊆ A j) :
    ∀ p : S, ∃ W : Set (Affine n), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine m), IsOpen D ∧ IsPreconnected D ∧
      ∃ e : Biholomorph W D, ∀ᶠ j in atTop,
        HolomorphicOnSubset W (fun x => f j x) ∧
        ∀ z ∈ D, (fderiv ℂ
          (f j ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0 := by
  intro p
  obtain ⟨j,hj⟩ := (hcover {p.val} isCompact_singleton
    (singleton_subset_iff.mpr p.property)).exists
  have hpj : p.val ∈ A j := hj (mem_singleton p.val)
  let q : A j := ⟨p.val,hpj⟩
  let z := ((b j).toHomeomorph q).val
  obtain ⟨R,hR,hRB⟩ := Metric.mem_nhds_iff.mp
    ((hBo j).mem_nhds ((b j).toHomeomorph q).property)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrB : closedBall z r ⊆ B j :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans hRB
  let W : Set (Affine n) := {x | x ∈ A j ∧ f j x ∈ ball z r}
  have hWA : W ⊆ A j := fun _ hx => hx.1
  have hfc : Continuous (fun x : A j => f j x.val) := by
    have heq : (fun x : A j => f j x.val) =
        (fun x : A j => ((b j).toHomeomorph x).val) := funext (hf j)
    rw [heq]
    exact continuous_subtype_val.comp (b j).toHomeomorph.continuous
  have hWo : IsOpen ((Subtype.val : A j → Affine n) ⁻¹' W) := by
    have heq : ((Subtype.val : A j → Affine n) ⁻¹' W) =
        {x : A j | f j x.val ∈ ball z r} := by
      ext x
      simp only [mem_preimage,W,mem_ofPred_eq,x.property,true_and]
    rw [heq]
    exact isOpen_ball.preimage hfc
  have hpW : p.val ∈ W := by
    refine ⟨hpj,?_⟩
    rw [hf j q]
    exact mem_ball_self hr
  have hrestrict : ∀ x : A j, x.val ∈ W ↔ ((b j).toHomeomorph x).val ∈ ball z r := by
    intro x
    simp only [W,mem_ofPred_eq,x.property,true_and,hf j x]
  let e := (b j).restrict hWA (ball_subset_closedBall.trans hrB) hrestrict
  let E := ambientExtend (fun x : B j => ((b j).toHomeomorph.symm x).val)
  have hEc : ContinuousOn E (B j) := continuousOn_ambientExtend
    (continuous_subtype_val.comp (b j).toHomeomorph.symm.continuous)
  have hEm : MapsTo E (B j) (A j) := by
    intro x hx
    rw [show E x = ((b j).toHomeomorph.symm ⟨x,hx⟩).val from ambientExtend_apply _ ⟨x,hx⟩]
    exact ((b j).toHomeomorph.symm ⟨x,hx⟩).property
  have hK : IsCompact (E '' closedBall z r) :=
    (isCompact_closedBall z r).image_of_continuousOn (hEc.mono hrB)
  have hKS : E '' closedBall z r ⊆ S := by
    rintro x ⟨y,hy,rfl⟩
    exact hAS j (hEm (hrB hy))
  have hWK : W ⊆ E '' closedBall z r := by
    intro x hx
    refine ⟨((b j).toHomeomorph ⟨x,hx.1⟩).val,?_,?_⟩
    · rw [← hf j ⟨x,hx.1⟩]
      exact ball_subset_closedBall hx.2
    · dsimp only [E]
      rw [ambientExtend_apply _ ((b j).toHomeomorph ⟨x,hx.1⟩),
        (b j).toHomeomorph.symm_apply_apply]
  refine ⟨W,hWA.trans (hAS j),relative_open_trans (hAS j) hWA (hAo j) hWo,hpW,
    ball z r,isOpen_ball,(convex_ball z r).isPreconnected,e,?_⟩
  filter_upwards [hcover _ hK hKS] with i hi
  exact chart_jacobian_of_biholomorph (hWK.trans hi) isOpen_ball (hBo i) e (b i)
    (fun x => hf i ⟨x.val,hi (hWK x.property)⟩)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalingEmbeddedCharts
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem scaling_biholomorph_embedded_charts {n m : ℕ}
    {S : Set (Affine n)} {O : Set (Affine m)} {y₀ : Affine m}
    (hy₀ : y₀ ∈ O) (hconn : IsPreconnected S) (hO : IsOpen O)
    {T : ℕ → Set (Affine m)}
    {f : ℕ → Affine n → Affine m} {g : ℕ → Affine m → Affine n}
    {F : Affine n → Affine m} {G : Affine m → Affine n}
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hcharts : ∀ p : S, ∃ W : Set (Affine n), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine m), IsOpen D ∧ IsPreconnected D ∧
      ∃ e : Biholomorph W D, ∀ᶠ j in atTop,
        HolomorphicOnSubset W (fun x => f j x) ∧
        ∀ z ∈ D, (fderiv ℂ
          (f j ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0)
    (hGhol : AnalyticOnNhd ℂ G (connectedComponentIn O y₀))
    (hfmap : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, MapsTo (f j) K (T j))
    (hGmap : MapsTo G (connectedComponentIn O y₀) S)
    (hgmap : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, g j y ∈ S)
    (hright : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, f j (g j y) = y)
    (hleft : ∀ x ∈ S, ∀ᶠ j in atTop, g j (f j x) = x)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j) :
    Nonempty (Biholomorph S (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hFhol : HolomorphicOnSubset S (fun x => F x) := by
    apply holomorphicOnSubset_of_local
    intro p
    obtain ⟨W,hWS,hWo,hpW,D,hDo,_,e,he⟩ := hcharts p
    exact ⟨W,hWS,hWo,hpW,holomorphic_chart_limit hDo e
      (hf.mono hWS) (he.mono fun j hj => hj.1)⟩
  have hFc : ContinuousOn F S := continuousOn_iff_continuous_domRestrict.mpr hFhol.continuous
  have hGc := hGhol.continuousOn
  have hri : ∀ y ∈ connectedComponentIn O y₀, F (G y) = y := by
    intro y hy
    have ht : Tendsto (fun j => g j y) atTop (𝓝[S] G y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hg.tendsto_at hy,hgmap y hy⟩
    exact tendsto_nhds_unique
      (hf.tendsto_comp (hFc _ (hGmap hy)) (hGmap hy) ht)
      (tendsto_const_nhds.congr' ((hright y hy).mono fun j hj => hj.symm))
  have hli : ∀ x ∈ S, F x ∈ connectedComponentIn O y₀ → G (F x) = x := by
    intro x hx hxD
    have ht : Tendsto (fun j => f j x) atTop (𝓝[connectedComponentIn O y₀] F x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.tendsto_at hx,(hf.tendsto_at hx) (hD.mem_nhds hxD)⟩
    exact tendsto_nhds_unique (hg.tendsto_comp (hGc _ hxD) hxD ht)
      (tendsto_const_nhds.congr' ((hleft x hx).mono fun j hj => hj.symm))
  let A : Set S := {p | F p.val ∈ connectedComponentIn O y₀}
  have hAo : IsOpen A := hD.preimage hFhol.continuous
  have hAc : IsClosed A := by
    apply closure_subset_iff_isClosed.mp
    intro p hp
    obtain ⟨W,hWS,hWo,hpW,D,hDo,hDc,e,he⟩ := hcharts p
    obtain ⟨q,hqW,hqA⟩ := mem_closure_iff.mp hp _ hWo hpW
    have hFw := hFhol.restrict hWS
    have hanchor := chart_jacobian_ne_zero_of_left_inverse hDo hD e hFw hGhol
      (fun x hx => hli x (hWS hx)) (⟨q.val,hqW⟩ : W) hqA
    have hmap := chart_limit_mapsTo_of_anchor hWS hDo hDc e hf he hfmap hexcluded
      ⟨(e.toHomeomorph ⟨q.val,hqW⟩).val,(e.toHomeomorph ⟨q.val,hqW⟩).property,hanchor⟩
    let E := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
    have hEx (x : W) : E (e.toHomeomorph x).val = x.val := by
      dsimp only [E]
      rw [ambientExtend_apply _ (e.toHomeomorph x),e.toHomeomorph.symm_apply_apply]
    have hHa : AnalyticOnNhd ℂ (F ∘ E) D := analytic_comp_chart_inverse hDo e hFw
    have himage : (F ∘ E) '' D ⊆ connectedComponentIn O (F q.val) := by
      apply (hDc.image (F ∘ E) hHa.continuousOn).subset_connectedComponentIn
      · exact ⟨(e.toHomeomorph ⟨q.val,hqW⟩).val,(e.toHomeomorph ⟨q.val,hqW⟩).property,
          congrArg F (hEx ⟨q.val,hqW⟩)⟩
      · rintro y ⟨z,hz,rfl⟩
        have hzE : E z = (e.toHomeomorph.symm ⟨z,hz⟩).val := ambientExtend_apply _ ⟨z,hz⟩
        exact hmap (hzE ▸ (e.toHomeomorph.symm ⟨z,hz⟩).property)
    rw [← connectedComponentIn_eq hqA] at himage
    exact himage ⟨(e.toHomeomorph ⟨p.val,hpW⟩).val,(e.toHomeomorph ⟨p.val,hpW⟩).property,
      congrArg F (hEx ⟨p.val,hpW⟩)⟩
  have hbase : y₀ ∈ connectedComponentIn O y₀ := mem_connectedComponentIn hy₀
  have hAn : A.Nonempty := ⟨⟨G y₀,hGmap hbase⟩,by
    change F (G y₀) ∈ connectedComponentIn O y₀
    rw [hri y₀ hbase]
    exact hbase⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc,hAo⟩ hAn
  have hFm : MapsTo F S (connectedComponentIn O y₀) := by
    intro x hx
    exact show (⟨x,hx⟩ : S) ∈ A from huniv ▸ mem_univ _
  exact ⟨⟨homeomorphOfInverseOn hFc hGc hFm hGmap
    (fun x hx => hli x hx (hFm hx)) hri,hFhol,
    holomorphicOnSubset_of_analyticOnNhd_open hD hGhol⟩⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalingExpanding
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem scaling_biholomorph_expanding {n m : ℕ}
    {S : Set (Affine n)} {O : Set (Affine m)} {y₀ : Affine m}
    (hy₀ : y₀ ∈ O) (hconn : IsPreconnected S) (hO : IsOpen O)
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAS : ∀ j, A j ⊆ S)
    (hAo : ∀ j, IsOpen ((Subtype.val : S → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    {f : ℕ → Affine n → Affine m} {g : ℕ → Affine m → Affine n}
    {F : Affine n → Affine m} {G : Affine m → Affine n}
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hbg : ∀ j (y : B j), g j y.val = ((b j).toHomeomorph.symm y).val)
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hcoverA : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, K ⊆ A j)
    (hcoverB : ∀ K : Set (Affine m), IsCompact K → K ⊆ connectedComponentIn O y₀ →
      ∀ᶠ j in atTop, K ⊆ B j)
    (hGmap : MapsTo G (connectedComponentIn O y₀) S)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ B j) :
    Nonempty (Biholomorph S (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hgj : ∀ j, AnalyticOnNhd ℂ (g j) (B j) := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open (hBo j)
    intro p
    obtain ⟨V,hVo,hpV,φ,hφ,he⟩ := (b j).holomorphic_invFun p
    refine ⟨V,hVo,hpV,φ,hφ,?_⟩
    intro q hq
    change φ q.val = g j q.val
    rw [hbg j q]
    exact he q hq
  have hGhol : AnalyticOnNhd ℂ G (connectedComponentIn O y₀) := by
    apply analyticOnNhd_of_differentiableOn_affine hD
    apply differentiableOn_of_locally_uniform_limit hD hg
    intro y hy
    obtain ⟨R,hR,hRD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hy)
    have hclosed : closedBall y (R/2) ⊆ connectedComponentIn O y₀ :=
      (closedBall_subset_ball (by linarith)).trans hRD
    refine ⟨ball y (R/2),ball_mem_nhds y (half_pos hR),?_⟩
    filter_upwards [hcoverB _ (isCompact_closedBall _ _) hclosed] with j hj
    exact (hgj j).differentiableOn.mono (ball_subset_closedBall.trans hj)
  have hcoverAp : ∀ x ∈ S, ∀ᶠ j in atTop, x ∈ A j := by
    intro x hx
    exact (hcoverA {x} isCompact_singleton (singleton_subset_iff.mpr hx)).mono
      fun j hj => hj (mem_singleton x)
  have hcoverBp : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, y ∈ B j := by
    intro y hy
    exact (hcoverB {y} isCompact_singleton (singleton_subset_iff.mpr hy)).mono
      fun j hj => hj (mem_singleton y)
  refine scaling_biholomorph_embedded_charts (T := B) hy₀ hconn hO hf hg
    (expanding_biholomorphisms_charts A B hAS hAo hBo b f hbf hcoverA) hGhol ?_ hGmap ?_ ?_ ?_ ?_
  · intro K hK hKS
    filter_upwards [hcoverA K hK hKS] with j hj x hx
    rw [hbf j ⟨x,hj hx⟩]
    exact ((b j).toHomeomorph ⟨x,hj hx⟩).property
  · intro y hy
    filter_upwards [hcoverBp y hy] with j hj
    rw [hbg j ⟨y,hj⟩]
    exact hAS j ((b j).toHomeomorph.symm ⟨y,hj⟩).property
  · intro y hy
    filter_upwards [hcoverBp y hy] with j hj
    rw [hbg j ⟨y,hj⟩,hbf j ((b j).toHomeomorph.symm ⟨y,hj⟩),
      (b j).toHomeomorph.apply_symm_apply]
  · intro x hx
    filter_upwards [hcoverAp x hx] with j hj
    rw [hbf j ⟨x,hj⟩,hbg j ((b j).toHomeomorph ⟨x,hj⟩),
      (b j).toHomeomorph.symm_apply_apply]
  · exact hexcluded

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ForwardLocalDataCompact
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem bounded_cocompact_expanding_limit_mem {d n : ℕ} {Γ : Type*}
    (D : Set (Affine d)) (hD : IsOpen D) (hconn : IsPreconnected D)
    (U : Set (Affine n)) [LocallyCompactSpace U]
    (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (g : ℕ → Affine d → Affine n) (G : Affine d → Affine n) (x₀ : D)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, g j x₀.val ∈ Subtype.val '' C)
    (hlocal : ∀ x ∈ D, ∃ W : Set (Affine d), IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧
      ∀ᶠ j in atTop, AnalyticOnNhd ℂ (g j) W ∧ MapsTo (g j) W U)
    (hconv : ∀ x ∈ D, Tendsto (fun j => g j x) atTop (𝓝 (G x))) :
    MapsTo G D U := by
  classical
  obtain ⟨C,hC,hbaseC⟩ := hbase
  obtain ⟨j,hj⟩ := hbaseC.exists
  obtain ⟨u₀,_,_⟩ := hj
  let F : ℕ → D → U := fun j x => if hx : g j x.val ∈ U then ⟨g j x.val,hx⟩ else u₀
  have hFval {j : ℕ} {x : D} (hx : g j x.val ∈ U) : (F j x).val = g j x.val := by
    simp only [F,dite_eq_left hx]
  have hFbase : ∃ C' : Set U, IsCompact C' ∧ ∀ᶠ j in atTop, F j x₀ ∈ C' := by
    refine ⟨C,hC,?_⟩
    filter_upwards [hbaseC] with j hj
    obtain ⟨u,hu,he⟩ := hj
    have huval : g j x₀.val ∈ U := he ▸ u.property
    have hFhu : F j x₀ = u := Subtype.ext ((hFval huval).trans he.symm)
    exact hFhu ▸ hu
  have hFhol : LocallyEventuallyHolomorphic D U F atTop := by
    intro x
    obtain ⟨W,hWo,hxW,hWD,he⟩ := hlocal x.val x.property
    refine ⟨W,hWo,hxW,hWD,?_⟩
    filter_upwards [he] with j hj
    intro p
    refine ⟨W,hWo,p.property,g j,hj.1,?_⟩
    intro q _
    exact (hFval (x := ⟨q.val,hWD q.property⟩) (hj.2 q.property)).symm
  have hFconv : ∀ x : D, Tendsto (fun j => (F j x).val) atTop (𝓝 (G x.val)) := by
    intro x
    obtain ⟨W,_,hxW,_,he⟩ := hlocal x.val x.property
    apply (hconv x.val x.property).congr'
    filter_upwards [he] with j hj
    exact (hFval (hj.2 hxW)).symm
  have hmem := bounded_cocompact_holomorphic_family_limit D hD hconn U hbounded
    hhol K hK hrep F atTop x₀ hFbase hFhol (fun x => G x.val) hFconv
  intro x hx
  exact hmem ⟨x,hx⟩

theorem cocompact_scaling_biholomorph_of_limits {n m : ℕ} {Γ : Type*}
    {U : Set (Affine n)} [LocallyCompactSpace U]
    (hconn : IsPreconnected U) (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    {O : Set (Affine m)} {y₀ : Affine m} (hO : IsOpen O) (hy₀ : y₀ ∈ O)
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAU : ∀ j, A j ⊆ U)
    (hAo : ∀ j, IsOpen ((Subtype.val : U → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m) (g : ℕ → Affine m → Affine n)
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hbg : ∀ j (y : B j), g j y.val = ((b j).toHomeomorph.symm y).val)
    (F : Affine n → Affine m) (G : Affine m → Affine n)
    (hf : TendstoLocallyUniformlyOn f F atTop U)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hcoverA : ∀ C : Set (Affine n), IsCompact C → C ⊆ U → ∀ᶠ j in atTop, C ⊆ A j)
    (hcoverB : ∀ C : Set (Affine m), IsCompact C → C ⊆ connectedComponentIn O y₀ →
      ∀ᶠ j in atTop, C ⊆ B j)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, g j y₀ ∈ Subtype.val '' C)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ B j) :
    Nonempty (Biholomorph U (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hgj : ∀ j, AnalyticOnNhd ℂ (g j) (B j) := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open (hBo j)
    convert (b j).holomorphic_invFun using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    exact hbg j y
  have hgm : ∀ j, MapsTo (g j) (B j) U := by
    intro j y hy
    rw [hbg j ⟨y,hy⟩]
    exact hAU j ((b j).toHomeomorph.symm ⟨y,hy⟩).property
  have hGmap : MapsTo G (connectedComponentIn O y₀) U := by
    refine bounded_cocompact_expanding_limit_mem _ hD
      isPreconnected_connectedComponentIn U hbounded hhol K hK hrep g G
      ⟨y₀,mem_connectedComponentIn hy₀⟩ hbase ?_ ?_
    · intro y hy
      obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hy)
      have hclosed : closedBall y (r/2) ⊆ connectedComponentIn O y₀ :=
        (closedBall_subset_ball (by linarith)).trans hrD
      refine ⟨ball y (r/2),isOpen_ball,mem_ball_self (half_pos hr),
        ball_subset_closedBall.trans hclosed,?_⟩
      filter_upwards [hcoverB _ (isCompact_closedBall _ _) hclosed] with j hj
      exact ⟨(hgj j).mono (ball_subset_closedBall.trans hj),
        (hgm j).mono_left (ball_subset_closedBall.trans hj)⟩
    · intro y hy
      exact hg.tendsto_at hy
  exact scaling_biholomorph_expanding hy₀ hconn hO A B hAU hAo hBo b
    hbf hbg hf hg hcoverA hcoverB hGmap hexcluded

theorem smooth_of_expanding_biholomorphisms {n m : ℕ} {U : Set (Affine n)}
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAU : ∀ j, A j ⊆ U)
    (hAo : ∀ j, IsOpen ((Subtype.val : U → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (hcover : ∀ x ∈ U, ∀ᶠ j in atTop, x ∈ A j) : IsSmooth U := by
  intro x
  obtain ⟨j,hj⟩ := (hcover x.val x.property).exists
  exact ⟨m,A j,hAU j,hAo j,hj,B j,hBo j,⟨b j⟩⟩

theorem forward_local_data_of_compact_bounds {n m : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U]
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m)
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hcover : ∀ C : Set (Affine n), IsCompact C → C ⊆ U → ∀ᶠ j in atTop, C ⊆ A j)
    (hbound : ∀ C : Set (Affine n), IsCompact C → C ⊆ U →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop, ∀ x ∈ C, ‖f j x‖ ≤ M) :
    ∀ p : U, ∃ V : Set (Affine n), V ⊆ U ∧
      IsOpen ((Subtype.val : U → Affine n) ⁻¹' V) ∧ p.val ∈ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop,
        HolomorphicOnSubset V (fun x => f j x) ∧ ∀ y ∈ V, ‖f j y‖ ≤ M := by
  intro p
  obtain ⟨C,hC,hCp⟩ := exists_compact_mem_nhds p
  let V := Subtype.val '' interior C
  have hVU : V ⊆ U := by rintro x ⟨q,_,rfl⟩; exact q.property
  have hVo : IsOpen ((Subtype.val : U → Affine n) ⁻¹' V) := by
    rw [show ((Subtype.val : U → Affine n) ⁻¹' V) = interior C from
      preimage_image_eq _ Subtype.val_injective]
    exact isOpen_interior
  have hpV : p.val ∈ V := ⟨p,mem_interior_iff_mem_nhds.mpr hCp,rfl⟩
  have hCU : Subtype.val '' C ⊆ U := by rintro x ⟨q,_,rfl⟩; exact q.property
  have hVC : V ⊆ Subtype.val '' C := image_mono interior_subset
  have hC' := hC.image continuous_subtype_val
  obtain ⟨M,hM,hMbound⟩ := hbound _ hC' hCU
  refine ⟨V,hVU,hVo,hpV,M,hM,?_⟩
  filter_upwards [hcover _ hC' hCU,hMbound] with j hj hMj
  have hfhol : HolomorphicOnSubset (A j) (fun x => f j x) := by
    convert (b j).holomorphic_toFun using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact hbf j x
  exact ⟨hfhol.restrict (hVC.trans hj),fun y hy => hMj y (hVC hy)⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CocompactScaling
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem cocompact_scaling_biholomorph {n m : ℕ} {Γ : Type*}
    {U : Set (Affine n)} [LocallyCompactSpace U]
    (hconn : IsPreconnected U) (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {O : Set (Affine m)} {y₀ : Affine m} (hO : IsOpen O) (hy₀ : y₀ ∈ O)
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAU : ∀ j, A j ⊆ U)
    (hAo : ∀ j, IsOpen ((Subtype.val : U → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m) (g : ℕ → Affine m → Affine n)
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hbg : ∀ j (y : B j), g j y.val = ((b j).toHomeomorph.symm y).val)
    (hcoverA : ∀ C : Set (Affine n), IsCompact C → C ⊆ U → ∀ᶠ j in atTop, C ⊆ A j)
    (hcoverB : ∀ C : Set (Affine m), IsCompact C → C ⊆ connectedComponentIn O y₀ →
      ∀ᶠ j in atTop, C ⊆ B j)
    (hbound : ∀ C : Set (Affine n), IsCompact C → C ⊆ U →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop, ∀ x ∈ C, ‖f j x‖ ≤ M)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, g j y₀ ∈ Subtype.val '' C)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ B j) :
    Nonempty (Biholomorph U (connectedComponentIn O y₀)) := by
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  have hS : IsSmooth U := smooth_of_expanding_biholomorphisms A B hAU hAo hBo b (by
    intro x hx
    exact (hcoverA {x} isCompact_singleton (singleton_subset_iff.mpr hx)).mono
      fun j hj => hj (mem_singleton x))
  obtain ⟨F,_hFa,φ,hφ,hfconv⟩ := hS.montel_expanding f
    (forward_local_data_of_compact_bounds A B b f hbf hcoverA hbound)
  have hD := hO.connectedComponentIn (x := y₀)
  have hgj : ∀ j, AnalyticOnNhd ℂ (g j) (B j) := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open (hBo j)
    convert (b j).holomorphic_invFun using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    exact hbg j y
  obtain ⟨M,hM,hMU⟩ := hbounded.exists_pos_norm_le
  have hlocalg : ∀ x ∈ connectedComponentIn O y₀, ∃ r : ℝ, 0 < r ∧
      ∃ M : ℝ, 0 < M ∧ ball x r ⊆ connectedComponentIn O y₀ ∧
      ∀ᶠ j in atTop, DifferentiableOn ℂ (g (φ j)) (ball x r) ∧
        ∀ y ∈ ball x r, ‖g (φ j) y‖ ≤ M := by
    intro x hx
    obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
    have hclosed : closedBall x (r/2) ⊆ connectedComponentIn O y₀ :=
      (closedBall_subset_ball (by linarith)).trans hrD
    refine ⟨r/2,half_pos hr,M,hM,ball_subset_closedBall.trans hclosed,?_⟩
    filter_upwards [hφ.tendsto_atTop (hcoverB _ (isCompact_closedBall _ _) hclosed)] with j hj
    refine ⟨(hgj (φ j)).differentiableOn.mono (ball_subset_closedBall.trans hj),?_⟩
    intro y hy
    have hyB := hj (ball_subset_closedBall hy)
    rw [hbg (φ j) ⟨y,hyB⟩]
    exact hMU _ (hAU (φ j) ((b (φ j)).toHomeomorph.symm ⟨y,hyB⟩).property)
  obtain ⟨G,_hGa,ψ,hψ,hgconv⟩ := analytic_montel_expanding_domains hD
    (fun j => g (φ j)) hlocalg
  have hφψ : Tendsto (fun j => φ (ψ j)) atTop atTop :=
    hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have hfconv' : TendstoLocallyUniformlyOn (fun j => f (φ (ψ j))) F atTop U := by
    intro V hV x hx
    obtain ⟨W,hW,he⟩ := hfconv V hV x hx
    exact ⟨W,hW,hψ.tendsto_atTop he⟩
  apply cocompact_scaling_biholomorph_of_limits hconn hbounded hhol K hK hrep hO hy₀
    (fun j => A (φ (ψ j))) (fun j => B (φ (ψ j)))
    (fun j => hAU (φ (ψ j))) (fun j => hAo (φ (ψ j))) (fun j => hBo (φ (ψ j)))
    (fun j => b (φ (ψ j))) (fun j => f (φ (ψ j))) (fun j => g (φ (ψ j)))
    (fun j => hbf (φ (ψ j))) (fun j => hbg (φ (ψ j))) F G hfconv' hgconv
  · intro C hC hCU
    exact hφψ (hcoverA C hC hCU)
  · intro C hC hCD
    exact hφψ (hcoverB C hC hCD)
  · obtain ⟨C,hC,he⟩ := hbase
    exact ⟨C,hC,hφψ he⟩
  · intro y hy
    obtain ⟨a,ha,he⟩ := hexcluded y hy
    exact ⟨fun j => a (φ (ψ j)),ha.comp hφψ,hφψ he⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompactSupportRates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric Topology
open scoped Classical

theorem support_normal_ray_bound
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {k : ℕ}
    (Φ : E × F → H) {p : H} (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0=p)
    (h : Fin k → H → ℂ) (hh : ∀ i, AnalyticAt ℂ (h i) p)
    (hh0 : ∀ i, h i p=1) (w : F) :
    ∃ A > 0, ∃ τ > 0, ∀ t : ℝ, 0 < t → t < τ →
      ‖fun i => 1-h i (Φ (weightedScale t (0,w)))‖ ≤ A*t := by
  let f : E × F → (Fin k → ℂ) := fun z i => h i (Φ z)
  have hf : DifferentiableAt ℂ f 0 := (analyticAt_pi_iff.mpr
    fun i => ((hΦ0.symm ▸ hh i).comp hΦ)).differentiableAt
  obtain ⟨C,hC,hbound⟩ := hf.isBigO_sub.exists_pos
  have hr : ContinuousAt (fun t : ℝ => ((0 : E),t • w)) 0 :=
    continuousAt_const.prodMk (continuousAt_id.smul continuousAt_const)
  have he : ∀ᶠ t : ℝ in 𝓝 0,
      ‖f (0,t • w)-f 0‖ ≤ C*‖((0 : E),t • w)‖ := by
    have hr' : Tendsto (fun t : ℝ => ((0 : E),t • w)) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul,Prod.mk_zero_zero] using hr.tendsto
    have he' := hr' hbound.bound
    change ∀ᶠ t : ℝ in 𝓝 0, ‖f (0,t • w)-f 0‖ ≤ C*‖((0 : E),t • w)-0‖ at he'
    simpa only [sub_zero] using he'
  obtain ⟨τ,hτ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨C*(‖w‖+1),mul_pos hC (by positivity),τ,hτ,?_⟩
  intro t ht htτ
  have htb : t ∈ ball (0 : ℝ) τ := by
    simpa only [mem_ball,dist_zero_right, Real.norm_eq_abs,abs_of_pos ht] using htτ
  have heq : weightedScale t ((0 : E),w) = (0,t • w) := by simp [weightedScale]
  have hzero : f 0 = fun _ => 1 := by funext i; exact (congrArg (h i) hΦ0).trans (hh0 i)
  have hn : ‖fun i => 1-h i (Φ (weightedScale t (0,w)))‖ = ‖f (0,t • w)-f 0‖ := by
    rw [heq,hzero,← norm_neg]
    congr 1
    funext i
    simp only [Pi.neg_apply,Pi.sub_apply,f,neg_sub]
  rw [hn]
  calc
    _ ≤ C*‖((0 : E),t • w)‖ := hball htb
    _ = C*(t*‖w‖) := by
      rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _),norm_smul,
        Real.norm_eq_abs,abs_of_pos ht]
    _ ≤ C*(‖w‖+1)*t := by nlinarith [hC,ht]

end

open Set Filter Topology
open scoped Classical

theorem IsSmooth.compact_support_rates {n k : ℕ} {U : Set (Affine n)}
    [Nonempty U] [PreconnectedSpace U] (hU : IsSmooth U)
    {K : Set U} (hK : IsCompact K)
    (h : Fin k → Affine n → ℂ) (hh : ∀ i, Differentiable ℂ (h i))
    (hb : ∀ i z, z ∈ U → ‖h i z‖ ≤ 1)
    (f : ℕ → U → U)
    (hf : ∀ j, HolomorphicOnSubset U (fun y => (f j y).val))
    (a : ℕ → U) (ha : ∀ j, a j ∈ K)
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j) {A : ℝ} (hA : 0 < A)
    (hbase : ∀ᶠ j in atTop, ‖fun i => 1-h i (f j (a j)).val‖ ≤ A*t j)
    {E : Set (Affine n)} (hE : IsCompact E) (hEU : E ⊆ U) :
    ∃ C > 0, ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
      ‖fun i => 1-h i (f j y).val‖ ≤ C*t j := by
  let E' : Set U := Subtype.val ⁻¹' E
  have hE' : IsCompact E' := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' E'=E := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩; exact hz
      · intro hy; exact ⟨⟨y,hEU hy⟩,hy,rfl⟩
    rw [he]
    exact hE
  obtain ⟨B,hB,hbound⟩ := hU.compact_peak_ratio hK hE'
  refine ⟨B*A,mul_pos hB hA,?_⟩
  filter_upwards [hbase] with j hj y hy
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_pos hB hA).le (ht j).le)).mpr
  intro i
  calc
    _ ≤ B*‖1-h i (f j (a j)).val‖ := hbound (h i) (hh i) (hb i) (f j) (hf j)
      (a j) (ha j) y hy
    _ ≤ B*‖fun i => 1-h i (f j (a j)).val‖ :=
      mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => (1 : ℂ)-h i (f j (a j)).val) i) hB.le
    _ ≤ B*(A*t j) := mul_le_mul_of_nonneg_left hj hB.le
    _ = (B*A)*t j := by ring

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OldOffsetOldPosition
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

 theorem oldPosition_inverse (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.chart.inverse (c.oldPosition (c.normal.parameters x)) = q x := by
  simpa only [oldPosition,c.normal.parameters.left_inv hgood.1] using
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.2

 theorem oldPosition_projection (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) : c.oldPosition (c.normal.parameters x) = c.chart.projection (q x-q c.center) := by
  have h := c.chart.left_inverse (c.oldPosition (c.normal.parameters x))
    (c.graph_boundary (c.normal.parameters x) hgood.2.1).2.1
  rw [c.oldPosition_inverse hgood] at h
  exact h.symm

end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ForwardBackwardGerm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

@[simp] theorem forward_zero (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.forward 0=q x := by
  simpa only [forward,map_zero,zero_add] using c.oldPosition_inverse hgood

@[simp] theorem backward_center (s : NashBoundaryScalingChart c x) (hgood : c.GoodAt x) :
    s.backward (q x)=0 := by
  simp only [backward,← c.oldPosition_projection hgood,sub_self,map_zero]

theorem forward_mem_variety (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    {z : Affine s.tangentDim × Affine s.normalDim} (hz : z ∈ s.offsets.source) :
    s.forward z ∈ V := c.chart.inverse_mem _ (hcut z hz).2.1

end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalScaleBound
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Matrix

theorem independent_real_rows_complex_injective {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) :
    Function.Injective (fun w : Fin k → ℂ => fun j => ∑ i, (β j i : ℂ)*w i) := by
  classical
  have hr : Matrix.det (Matrix.of β) ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.Nonsingular.of_linearIndependent_row hβ)
  let A : Matrix (Fin k) (Fin k) ℂ := Complex.ofRealHom.mapMatrix (Matrix.of β)
  have hc : A.det ≠ 0 := by
    dsimp [A]
    rw [←RingHom.map_det]
    simpa using hr
  have hi := Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero hc)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem independent_real_rows_bound {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin k → ℂ,
      ‖w‖ ≤ C*‖(fun j => ∑ i, (β j i : ℂ)*w i)‖ := by
  classical
  let L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    Matrix.mulVecLin (Matrix.of (fun j i => (β j i : ℂ)))
  have hi : Function.Injective L := by
    convert independent_real_rows_complex_injective β hβ using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  let e : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ) :=
    (LinearEquiv.ofBijective L ⟨hi,(LinearMap.injective_iff_surjective.mp hi)⟩).toContinuousLinearEquiv
  refine ⟨‖e.symm.toContinuousLinearMap‖+1,by positivity,?_⟩
  intro w
  have h := e.symm.toContinuousLinearMap.le_opNorm (e w)
  have he : e w = fun j => ∑ i, (β j i : ℂ)*w i := by
    rfl
  calc
    ‖w‖ ≤ ‖e.symm.toContinuousLinearMap‖*‖e w‖ := by simpa using h
    _ ≤ (‖e.symm.toContinuousLinearMap‖+1)*‖e w‖ := by gcongr; linarith
    _ = _ := by rw [he]

end

open Set Filter Asymptotics
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem analytic_quadratic_remainder {f : E → F} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) :
    (fun x => f x - fderiv ℂ f 0 x) =O[𝓝 0] (fun x => ‖x‖^2) := by
  obtain ⟨p,hp⟩ := hf
  have he : ∀ x, p.partialSum 2 x = fderiv ℂ f 0 x := by
    intro x
    simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,hp.coeff_zero,hf0]
    rw [hp.hasFDerivAt.fderiv,continuousMultilinearCurryFin1_apply]
    congr 1
  simpa only [zero_add,he] using hp.isBigO_sub_partialSum_pow 2

theorem normal_scale_bound {k : ℕ} (β : Fin k → Fin k → ℝ)
    (hβ : LinearIndependent ℝ β)
    (f : Fin k → E × (Fin k → ℂ) → ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) 0) (hf0 : ∀ i, f i 0 = 0)
    (hder : ∀ i x, fderiv ℂ (f i) 0 x = Complex.I*∑ j, (β i j : ℂ)*x.2 j) :
    ∃ C > 0, ∃ V ∈ 𝓝 (0 : E × (Fin k → ℂ)),
      ∀ x ∈ V, ‖x.2‖ ≤ C*(‖fun i => f i x‖+‖x‖^2) := by
  classical
  have ho : ∀ i, (fun x => f i x-fderiv ℂ (f i) 0 x) =O[𝓝 0]
      (fun x => ‖x‖^2) := fun i => analytic_quadratic_remainder (hf i) (hf0 i)
  choose C hC hbound using fun i => (ho i).exists_pos
  let M : ℝ := ∑ i, C i
  have hM (i : Fin k) : C i ≤ M := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hev : ∀ᶠ x in 𝓝 (0 : E × (Fin k → ℂ)), ∀ i,
      ‖f i x-fderiv ℂ (f i) 0 x‖ ≤ M*‖x‖^2 := by
    have hh : ∀ᶠ x in 𝓝 (0 : E × (Fin k → ℂ)), ∀ i,
      ‖f i x-fderiv ℂ (f i) 0 x‖ ≤ C i*‖x‖^2 := by
      apply Filter.eventually_all.mpr
      intro i
      simpa only [norm_pow,norm_norm] using (hbound i).bound
    exact hh.mono fun x hx i => (hx i).trans (mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _))
  obtain ⟨D,hD,hd⟩ := independent_real_rows_bound β hβ
  refine ⟨D*(M+1),mul_pos hD (by positivity),{x | ∀ i,
    ‖f i x-fderiv ℂ (f i) 0 x‖ ≤ M*‖x‖^2},hev,?_⟩
  intro x hx
  have hrow : ‖(fun i => ∑ j, (β i j : ℂ)*x.2 j)‖ ≤ ‖fun i => f i x‖+M*‖x‖^2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hh := norm_le_norm_sub_add (fderiv ℂ (f i) 0 x) (f i x)
    rw [norm_sub_rev] at hh
    have hn : ‖fderiv ℂ (f i) 0 x‖ = ‖∑ j, (β i j : ℂ)*x.2 j‖ := by
      rw [hder,norm_mul,Complex.norm_I,one_mul]
    rw [hn] at hh
    have hfi := norm_le_pi_norm (fun i => f i x) i
    linarith [hx i]
  calc
    ‖x.2‖ ≤ D*‖(fun i => ∑ j, (β i j : ℂ)*x.2 j)‖ := hd x.2
    _ ≤ D*(‖fun i => f i x‖+M*‖x‖^2) := mul_le_mul_of_nonneg_left hrow hD.le
    _ ≤ D*(M+1)*(‖fun i => f i x‖+‖x‖^2) := by
      have hn := norm_nonneg (fun i => f i x)
      have hx0 := sq_nonneg ‖x‖
      nlinarith [mul_nonneg hM0 hn]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentSupportCoercivity
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Asymptotics
open scoped Topology

theorem log_near_one_bound : ∃ A > 0, ∀ᶠ z : ℂ in 𝓝 1,
    z ≠ 0 ∧ ‖Complex.log z‖ ≤ A*‖z-1‖ := by
  obtain ⟨A,hA,ha⟩ := (Complex.differentiableAt_log Complex.one_mem_slitPlane).isBigO_sub.exists_pos
  refine ⟨A,hA,?_⟩
  filter_upwards [ha.bound, isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with z hz hne
  exact ⟨hne,by simpa only [Complex.log_one,sub_zero] using hz⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InverseChartGaussian
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weightedUnscale_bound {M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    {x : E × F} (hx : ‖x‖^2 ≤ M*t) (hw : ‖x.2‖ ≤ M*t) :
    ‖weightedUnscale t x‖ ≤ max (Real.sqrt M) M := by
  have hs : ‖x.1‖ ≤ Real.sqrt M*Real.sqrt t := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hM,Real.sq_sqrt ht.le]
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le x)).trans hx
  rw [weightedUnscale,Prod.norm_def,max_le_iff]
  constructor
  · have hsr := Real.sqrt_pos.mpr ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hsr),mul_comm,←div_eq_mul_inv]
    exact ((div_le_iff₀ hsr).mpr hs).trans (le_max_left _ _)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),mul_comm,←div_eq_mul_inv]
    exact ((div_le_iff₀ ht).mpr hw).trans (le_max_right _ _)

end

open Set Filter Asymptotics
open scoped Topology

theorem gaussian_peak_localizes {E : Type*} [NormedAddCommGroup E]
    (h : E → ℂ) (D : Set E) (p : E)
    (hp : ∀ q ∈ D, ‖h q‖ ≤ Real.exp (-(‖q-p‖^2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ D, ‖1-h q‖ < δ → ‖q-p‖ < ε := by
  refine ⟨1-Real.exp (-(ε^2)),?_,?_⟩
  · have he : Real.exp (-(ε^2)) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos (sq_pos_of_pos hε))
    linarith
  · intro q hq hd
    by_contra hn
    have he : ε^2 ≤ ‖q-p‖^2 := (sq_le_sq₀ hε.le (norm_nonneg _)).mpr (le_of_not_gt hn)
    have hn' : ‖h q‖ ≤ Real.exp (-(ε^2)) :=
      (hp q hq).trans (Real.exp_le_exp.mpr (neg_le_neg he))
    have htri : (1 : ℝ) ≤ ‖1-h q‖+‖h q‖ := by
      simpa only [norm_one] using norm_le_norm_sub_add (1 : ℂ) (h q)
    linarith

theorem gaussian_peak_eventually_mem {E I A : Type*} [NormedAddCommGroup E]
    {l : Filter I} (h : E → ℂ) (D : Set E) (p : E)
    (hp : ∀ q ∈ D, ‖h q‖ ≤ Real.exp (-(‖q-p‖^2)))
    (x : I → A → E) (K : Set A) (t : I → ℝ) (ht : Tendsto t l (𝓝 0))
    {C : ℝ} (hx : ∀ᶠ i in l, ∀ a ∈ K, x i a ∈ D ∧ ‖1-h (x i a)‖ ≤ C*t i)
    {V : Set E} (hV : V ∈ 𝓝 p) :
    ∀ᶠ i in l, ∀ a ∈ K, x i a ∈ V := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨δ,hδ,hd⟩ := gaussian_peak_localizes h D p hp hε
  have ht' : Tendsto (fun i => C*t i) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have he := ht' (gt_mem_nhds hδ)
  filter_upwards [hx,he] with i hi hit a ha
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  exact hd _ (hi a ha).1 ((hi a ha).2.trans_lt hit)

theorem inverse_chart_gaussian {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {Φ : E → F} {Ψ : F → E} {p : F}
    (hΦ : ContinuousAt Φ 0) (hΦ0 : Φ 0 = p)
    (hΨ : DifferentiableAt ℂ Ψ p) (hΨ0 : Ψ p = 0)
    (hinv : ∀ᶠ x in 𝓝 (0 : E), Ψ (Φ x) = x)
    (h : F → ℂ) (D : Set F)
    (hpeak : ∀ q ∈ D, ‖h q‖ ≤ Real.exp (-(‖q-p‖^2))) :
    ∃ c > 0, ∀ᶠ x in 𝓝 (0 : E), Φ x ∈ D →
      ‖h (Φ x)‖ ≤ Real.exp (-c*‖x‖^2) := by
  obtain ⟨C,hC,hbound⟩ := hΨ.isBigO_sub.exists_pos
  have he : ∀ᶠ x in 𝓝 (0 : E), ‖Ψ (Φ x)‖ ≤ C*‖Φ x-p‖ := by
    have h := ((hΦ0 ▸ hΦ.tendsto) hbound.bound)
    change ∀ᶠ x in 𝓝 (0 : E), ‖Ψ (Φ x)-Ψ p‖ ≤ C*‖Φ x-p‖ at h
    simpa only [hΨ0,sub_zero] using h
  refine ⟨1/C^2,by positivity,?_⟩
  filter_upwards [he,hinv] with x hx hi hxD
  rw [hi] at hx
  have hs : ‖x‖^2 ≤ C^2*‖Φ x-p‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx
  have hs' : (1/C^2)*‖x‖^2 ≤ ‖Φ x-p‖^2 := by
    rw [one_div,mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ (sq_pos_of_pos hC)).mpr (by nlinarith [hs])
  exact (hpeak _ hxD).trans (Real.exp_le_exp.mpr (by nlinarith [hs']))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalInverseSupportScaled
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter
open scoped Topology
theorem independent_support_coercivity_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (h : Fin k → E × (Fin k → ℂ) → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) 0) (hh0 : ∀ i, h i 0 = 1)
    (hder : ∀ i x, fderiv ℂ (fun y => Complex.log (h i y)) 0 x =
      Complex.I*∑ j, (β i j : ℂ)*x.2 j)
    (D : Set (E × (Fin k → ℂ))) {c : ℝ} (hc : 0 < c)
    (i₀ : Fin k) (hpeak : ∀ x ∈ D, ‖h i₀ x‖ ≤ Real.exp (-c*‖x‖^2)) :
    ∃ C > 0, ∃ V ∈ 𝓝 (0 : E × (Fin k → ℂ)), ∀ x ∈ V, x ∈ D →
      ‖x‖^2 ≤ C*‖fun i => 1-h i x‖ ∧ ‖x.2‖ ≤ C*‖fun i => 1-h i x‖ := by
  classical
  obtain ⟨A,hA,hlog⟩ := log_near_one_bound
  have he : ∀ᶠ x in 𝓝 (0 : E × (Fin k → ℂ)), ∀ i,
      h i x ≠ 0 ∧ ‖Complex.log (h i x)‖ ≤ A*‖h i x-1‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hh0 i) ▸ (hh i).continuousAt.tendsto) hlog
  have hal : ∀ i, AnalyticAt ℂ (fun x => Complex.log (h i x)) 0 :=
    fun i => (hh i).clog (by rw [hh0]; exact Complex.one_mem_slitPlane)
  obtain ⟨B,hB,W,hW,hscale⟩ := normal_scale_bound β hβ
    (fun i x => Complex.log (h i x)) hal (by simp [hh0]) hder
  refine ⟨max (A/c) (B*(A+A/c)), lt_of_lt_of_le (div_pos hA hc) (le_max_left _ _),
    W ∩ {x | ∀ i, h i x ≠ 0 ∧ ‖Complex.log (h i x)‖ ≤ A*‖h i x-1‖},
    inter_mem hW he,?_⟩
  intro x hx hxD
  let d := ‖fun i => (1 : ℂ)-h i x‖
  have hd : 0 ≤ d := norm_nonneg _
  have hld : ‖fun i => Complex.log (h i x)‖ ≤ A*d := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA.le hd)).mpr
    intro i
    calc
      _ ≤ A*‖h i x-1‖ := (hx.2 i).2
      _ = A*‖1-h i x‖ := by rw [norm_sub_rev]
      _ ≤ A*d := mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => (1 : ℂ)-h i x) i) hA.le
  have hreal : (Complex.log (h i₀ x)).re ≤ -c*‖x‖^2 := by
    rw [Complex.log_re]
    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hx.2 i₀).1)).mpr (hpeak x hxD)
  have hs : ‖x‖^2 ≤ (A/c)*d := by
    have hr := Complex.abs_re_le_norm (Complex.log (h i₀ x))
    have hnorm : ‖Complex.log (h i₀ x)‖ ≤ A*d :=
      (norm_le_pi_norm (fun i => Complex.log (h i x)) i₀).trans hld
    have hh' : c*‖x‖^2 ≤ A*d := by
      have habs := neg_le_abs (Complex.log (h i₀ x)).re
      linarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hh']
  constructor
  · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  · calc
      ‖x.2‖ ≤ B*(‖fun i => Complex.log (h i x)‖+‖x‖^2) := hscale x hx.1
      _ ≤ B*(A*d+(A/c)*d) := mul_le_mul_of_nonneg_left (add_le_add hld hs) hB.le
      _ = (B*(A+A/c))*d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hd

theorem local_inverse_support_scaled_bound
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {k : ℕ}
    (Φ : E × (Fin k → ℂ) → H) (Ψ : H → E × (Fin k → ℂ)) {p : H}
    (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0=p)
    (hΨ : DifferentiableAt ℂ Ψ p) (hΨ0 : Ψ p=0)
    (hinv : ∀ᶠ z in 𝓝 (0 : E × (Fin k → ℂ)), Ψ (Φ z)=z)
    (D : Set H) (h : Fin k → H → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) p) (hh0 : ∀ i, h i p=1)
    (i₀ : Fin k) (hpeak : ∀ y ∈ D, ‖h i₀ y‖ ≤ Real.exp (-(‖y-p‖^2)))
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (Φ y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j) :
    ∃ C > 0, ∃ W ∈ 𝓝 (0 : E × (Fin k → ℂ)),
      ∀ A ≥ 0, ∀ t > 0, ∀ z ∈ W, Φ z ∈ D →
        ‖fun i => 1-h i (Φ z)‖ ≤ A*t →
        ‖weightedUnscale t z‖ ≤ max (Real.sqrt (C*A)) (C*A) := by
  obtain ⟨c,hc,hev⟩ := inverse_chart_gaussian hΦ.continuousAt hΦ0 hΨ hΨ0 hinv
    (h i₀) D hpeak
  let R := {z | Φ z ∈ D → ‖h i₀ (Φ z)‖ ≤ Real.exp (-c*‖z‖^2)}
  have hR : R ∈ 𝓝 (0 : E × (Fin k → ℂ)) := hev
  obtain ⟨C,hC,W,hW,hb⟩ := independent_support_coercivity_at β hβ
    (fun i z => h i (Φ z)) (fun i => (hΦ0.symm ▸ hh i).comp hΦ)
    (by intro i; rw [hΦ0,hh0]) (by exact hder) (R ∩ Φ ⁻¹' D) hc i₀
    (fun z hz => hz.1 hz.2)
  refine ⟨C,hC,W ∩ R,inter_mem hW hR,?_⟩
  intro A hA t ht z hz hzD hd
  have H := hb z hz.1 ⟨hz.2,hzD⟩
  have hd' : C*‖fun i => 1-h i (Φ z)‖ ≤ (C*A)*t := by
    calc _ ≤ C*(A*t) := mul_le_mul_of_nonneg_left hd hC.le
         _ = _ := by ring
  exact weightedUnscale_bound (mul_nonneg hC.le hA) ht (H.1.trans hd') (H.2.trans hd')
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalizedLocalInverse
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

lemma actionLocalSet_open {n : ℕ} {U : Set (Affine n)} {Γ : Type*}
    [Group Γ] [MulAction Γ U] [ContinuousConstSMul Γ U]
    (γ : Γ) {Ω : Set (Affine n)}
    (hΩ : IsOpen ((Subtype.val : U → Affine n) ⁻¹' Ω)) :
    IsOpen ((Subtype.val : U → Affine n) ⁻¹' actionLocalSet U Γ γ Ω) := by
  have he : (Subtype.val : U → Affine n) ⁻¹' actionLocalSet U Γ γ Ω =
      (fun y : U => γ • y) ⁻¹' ((Subtype.val : U → Affine n) ⁻¹' Ω) := by
    ext y
    simp only [actionLocalSet,mem_preimage,mem_inter_iff,y.property,true_and,
      ambientAction_subtype]
  rw [he]
  exact hΩ.preimage (continuous_const_smul γ)

lemma normalizedLocalBiholomorph_forward {n m : ℕ} {U Ω : Set (Affine n)}
    {D : Set (Affine m)} {Γ : Type*} [Group Γ] [MulAction Γ U]
    [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (γ : Γ) (b : Biholomorph (U ∩ Ω) D) (f : Affine n → Affine m)
    (hf : ∀ y : ↥(U ∩ Ω), f y.val=(b.toHomeomorph y).val)
    (y : actionLocalSet U Γ γ Ω) :
    f (ambientAction U Γ γ y.val) =
      ((normalizedLocalBiholomorph hhol γ b).toHomeomorph y).val := by
  have he : ambientAction U Γ γ y.val = (γ • (⟨y.val,y.property.1⟩ : U)).val := by
    exact ambientAction_subtype γ ⟨y.val,y.property.1⟩
  rw [he]
  exact hf ⟨(γ • (⟨y.val,y.property.1⟩ : U)).val,
    ⟨(γ • (⟨y.val,y.property.1⟩ : U)).property,he ▸ y.property.2⟩⟩

lemma normalizedLocalBiholomorph_inverse {n m : ℕ} {U Ω : Set (Affine n)}
    {D : Set (Affine m)} {Γ : Type*} [Group Γ] [MulAction Γ U]
    [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (γ : Γ) (b : Biholomorph (U ∩ Ω) D) (g : Affine m → Affine n)
    (hg : ∀ y : D, g y.val=(b.toHomeomorph.symm y).val) (y : D) :
    ambientAction U Γ γ⁻¹ (g y.val) =
      ((normalizedLocalBiholomorph hhol γ b).toHomeomorph.symm y).val := by
  rw [hg y]
  exact ambientAction_subtype γ⁻¹ ⟨(b.toHomeomorph.symm y).val,
    (b.toHomeomorph.symm y).property.1⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

lemma domain_open (s : NashBoundaryScalingChart c x) (hcut : s.HasCutoffs)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U)) (t : ℝ) : IsOpen (s.domain t) := by
  let f : s.offsets.source → V := fun z => ⟨s.forward z,s.forward_mem_variety hcut z.property⟩
  have hf : Continuous f := ((continuousOn_iff_continuous_domRestrict.mp
    (s.forward_analytic hcut).continuousOn)).subtype_mk _
  have ho := (s.offsets.open_source.isOpenMap_subtype_val) _ (hU.preimage hf)
  have he : (Subtype.val : s.offsets.source → Affine s.tangentDim × Affine s.normalDim) ''
      (f ⁻¹' ((Subtype.val : V → Affine N) ⁻¹' U)) =
      {z | z ∈ s.offsets.source ∧ s.forward z ∈ U} := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩; exact ⟨y.property,hy⟩
    · rintro ⟨hz,hy⟩; exact ⟨⟨z,hz⟩,hy,rfl⟩
  rw [he] at ho
  exact ho.preimage (continuous_iff_continuousAt.mpr fun z => (weightedScale_analytic t z).continuousAt)

end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GlobalTwoSided
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical

theorem support_rates_imply_scaled_localization
    {N r k : ℕ} {U V Ω : Set (Affine N)} (hUV : U ⊆ V)
    (Φ : Affine r × Affine k → Affine N) (Ψ : Affine N → Affine r × Affine k)
    {p : Affine N} (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0=p)
    (hΨ : DifferentiableAt ℂ Ψ p) (hΨ0 : Ψ p=0)
    (hinv : ∀ᶠ z in 𝓝 (0 : Affine r × Affine k), Ψ (Φ z)=z)
    (hΩ : Ω ∈ 𝓝[V] p) (hfg : ∀ y ∈ Ω, Φ (Ψ y)=y)
    (h : Fin k → Affine N → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) p) (hh0 : ∀ i, h i p=1)
    (i₀ : Fin k) (hpeak : ∀ y ∈ U, ‖h i₀ y‖ ≤ Real.exp (-(‖y-p‖^2)))
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (Φ y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j)
    (f : ℕ → U → U) (t : ℕ → ℝ) (htp : ∀ j, 0 < t j)
    (ht : Tendsto t atTop (𝓝 0)) (E : Set (Affine N))
    {A : ℝ} (hA : 0 < A)
    (hrate : ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
      ‖fun i => 1-h i (f j y).val‖ ≤ A*t j) :
    ∃ M > 0, ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
      (f j y).val ∈ Ω ∧ ‖weightedUnscale (t j) (Ψ (f j y).val)‖ ≤ M := by
  obtain ⟨C,hC,W,hW,hscale⟩ := local_inverse_support_scaled_bound Φ Ψ hΦ hΦ0
    hΨ hΨ0 hinv U h hh hh0 i₀ hpeak β hβ hder
  obtain ⟨WΩ,hWΩ,hinc⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hΩ
  have hWΨ : Ψ ⁻¹' W ∈ 𝓝 p := hΨ.continuousAt.preimage_mem_nhds (hΨ0.symm ▸ hW)
  have hl := gaussian_peak_eventually_mem (h i₀) U p hpeak
    (fun j (y : U) => (f j y).val) {y : U | y.val ∈ E} t ht
    (C := A) (hrate.mono fun j hj y hy =>
      ⟨(f j y).property,(norm_le_pi_norm (fun i => (1 : ℂ)-h i (f j y).val) i₀).trans (hj y hy)⟩) (inter_mem hWΩ hWΨ)
  let M := max (Real.sqrt (C*A)) (C*A)
  refine ⟨M+1,by dsimp only [M]; positivity,?_⟩
  filter_upwards [hl,hrate] with j hj hr y hy
  have hym := hj y hy
  have hyΩ : (f j y).val ∈ Ω := hinc ⟨hym.1,hUV (f j y).property⟩
  have hb := hscale A hA.le (t j) (htp j) (Ψ (f j y).val) hym.2
    (by rw [hfg _ hyΩ]; exact (f j y).property)
    (by rw [hfg _ hyΩ]; exact hr y hy)
  exact ⟨hyΩ,hb.trans (by dsimp only [M]; linarith)⟩

end

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem global_from_two_sided_oai (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hcut : s.HasCutoffs)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U) (hsmooth : IsSmooth U)
    [LocallyCompactSpace U] (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (Ω : Set (Affine N)) (hΩV : Ω ⊆ V)
    (hΩo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' Ω)) (hpΩ : q x ∈ Ω)
    (hfΩ : MapsTo s.forward s.offsets.source Ω)
    (hgS : MapsTo s.backward Ω s.offsets.source)
    (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y)
    (h : Fin s.normalDim → Affine N → ℂ)
    (hh : ∀ i, Differentiable ℂ (h i)) (hh0 : ∀ i, h i (q x)=1)
    (hb : ∀ i y, y ∈ U → ‖h i y‖ ≤ 1)
    (i₀ : Fin s.normalDim)
    (hpeak : ∀ y ∈ U, ‖h i₀ y‖ ≤ Real.exp (-(‖y-q x‖^2)))
    (β : Fin s.normalDim → Fin s.normalDim → ℝ) (hβ : LinearIndependent ℝ β)
    (hder : ∀ i z, fderiv ℂ (fun y => Complex.log (h i (s.forward y))) 0 z =
      Complex.I*∑ j, (β i j : ℂ)*z.2 j)
    (O : Set (Affine s.tangentDim × Affine s.normalDim)) (hO : IsOpen O)
    (w : Affine s.normalDim) (hw : (0,w) ∈ O)
    (hcover : ∀ K : Set (Affine s.tangentDim × Affine s.normalDim),
      IsCompact K → K ⊆ O → ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ s.domain t)
    (hexclude : ∀ z ∉ O, ∀ t : ℕ → ℝ, Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      ∃ a : ℕ → Affine s.tangentDim × Affine s.normalDim,
        Tendsto a atTop (𝓝 z) ∧ ∀ᶠ j in atTop, a j ∉ s.domain (t j)) :
    Nonempty (Biholomorph U (connectedComponentIn
      ((affineProductCoordinates s.tangentDim s.normalDim) '' O)
      ((affineProductCoordinates s.tangentDim s.normalDim) (0,w)))) := by
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  let : Nonempty U := hconn.nonempty.to_subtype
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn.isPreconnected
  let e := affineProductCoordinates s.tangentDim s.normalDim
  have hsf := s.forward_analytic hcut 0 s.source_zero
  have hsg := (s.backward_analytic (q x) (mem_univ _)).differentiableAt
  have hs0 := s.forward_zero hgood
  have hg0 := s.backward_center hgood
  have hinv : ∀ᶠ z in 𝓝 (0 : Affine s.tangentDim × Affine s.normalDim),
      s.backward (s.forward z)=z := by
    filter_upwards [s.offsets.open_source.mem_nhds s.source_zero] with z hz
    exact s.backward_forward hcut hz
  have hΩn : Ω ∈ 𝓝[V] (q x) := by
    rw [nhdsWithin_eq_map_subtype_coe (hΩV hpΩ)]
    exact hΩo.mem_nhds hpΩ
  have hha : ∀ i, AnalyticAt ℂ (h i) (q x) := fun i => analyticOnNhd_of_differentiableOn_finite isOpen_univ (hh i).differentiableOn _ (mem_univ _)
  obtain ⟨A,hA,τ,hτ,hanchor⟩ := support_normal_ray_bound s.forward hsf hs0 h hha hh0 w
  have hbaseD : ∀ᶠ t : ℝ in 𝓝[>] 0, (0,w) ∈ s.domain t :=
    (hcover {(0,w)} isCompact_singleton (singleton_subset_iff.mpr hw)).mono
      fun t ht => ht (mem_singleton _)
  obtain ⟨δ,hδ,hδD⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbaseD
  obtain ⟨t,_htanti,htmem,ht⟩ := exists_seq_strictAnti_tendsto' (lt_min hδ hτ)
  have htp : ∀ j, 0 < t j := fun j => (htmem j).1
  have htD : ∀ j, (0,w) ∈ s.domain (t j) :=
    fun j => hδD ⟨(htmem j).1,lt_of_lt_of_le (htmem j).2 (min_le_left _ _)⟩
  let p : ℕ → U := fun j => ⟨s.forward (weightedScale (t j) (0,w)),(htD j).2⟩
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  choose a ha γ hγ using fun j => hrep (p j)
  have hanchor' : ∀ᶠ j in atTop, ‖fun i => 1-h i (γ j • a j : U).val‖ ≤ A*t j := by
    apply Eventually.of_forall
    intro j
    rw [hγ j]
    exact hanchor (t j) (htp j) (lt_of_lt_of_le (htmem j).2 (min_le_right _ _))
  have hest : ∀ E : Set (Affine N), IsCompact E → E ⊆ U →
      ∃ M > 0, ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
        (γ j • y : U).val ∈ Ω ∧
        ‖weightedUnscale (t j) (s.backward (γ j • y : U).val)‖ ≤ M := by
    intro E hE hEU
    obtain ⟨C,hC,hrate⟩ := hsmooth.compact_support_rates hK h hh hb
      (fun j y => γ j • y) (fun j => hhol (γ j)) a ha t htp hA hanchor' hE hEU
    exact support_rates_imply_scaled_localization hUV s.forward s.backward hsf hs0
      hsg hg0 hinv hΩn hfg h hha hh0 i₀ hpeak β hβ hder
      (fun j y => γ j • y) t htp ht E hC hrate
  let D : ℕ → Set (Affine (s.tangentDim+s.normalDim)) := fun j => e '' s.domain (t j)
  let Aset : ℕ → Set (Affine N) := fun j => actionLocalSet U Γ (γ j) Ω
  let b : ∀ j, Biholomorph (Aset j) (D j) := fun j =>
    normalizedLocalBiholomorph hhol (γ j)
      (s.scaled_local_biholomorph hcut Ω hfΩ hgS hfg (htp j))
  let F : ℕ → Affine N → Affine (s.tangentDim+s.normalDim) :=
    fun j y => e (weightedUnscale (t j) (s.backward (ambientAction U Γ (γ j) y)))
  let G : ℕ → Affine (s.tangentDim+s.normalDim) → Affine N :=
    fun j z => ambientAction U Γ (γ j)⁻¹ (s.forward (weightedScale (t j) (e.symm z)))
  have hAo : ∀ j, IsOpen ((Subtype.val : U → Affine N) ⁻¹' Aset j) := by
    intro j
    apply actionLocalSet_open (γ j)
    exact hΩo.preimage (Topology.IsEmbedding.inclusion hUV).continuous
  have hDo : ∀ j, IsOpen (D j) := fun j =>
    e.toHomeomorph.isOpenMap _ (s.domain_open hcut hU (t j))
  have hbf : ∀ j (y : Aset j), F j y.val=((b j).toHomeomorph y).val := by
    intro j y
    exact normalizedLocalBiholomorph_forward hhol (γ j)
      (s.scaled_local_biholomorph hcut Ω hfΩ hgS hfg (htp j))
      (fun y => e (weightedUnscale (t j) (s.backward y))) (by intro y; rfl) y
  have hbg : ∀ j (z : D j), G j z.val=((b j).toHomeomorph.symm z).val := by
    intro j z
    exact normalizedLocalBiholomorph_inverse hhol (γ j)
      (s.scaled_local_biholomorph hcut Ω hfΩ hgS hfg (htp j))
      (fun z => s.forward (weightedScale (t j) (e.symm z))) (by intro z; rfl) z
  have hcoverA : ∀ E, IsCompact E → E ⊆ U → ∀ᶠ j in atTop, E ⊆ Aset j := by
    intro E hE hEU
    obtain ⟨M,_hM,he⟩ := hest E hE hEU
    filter_upwards [he] with j hj y hy
    refine ⟨hEU hy,?_⟩
    change ambientAction U Γ (γ j) y ∈ Ω
    rw [show ambientAction U Γ (γ j) y=(γ j • (⟨y,hEU hy⟩ : U)).val from
      ambientAction_subtype (γ j) ⟨y,hEU hy⟩]
    exact (hj ⟨y,hEU hy⟩ hy).1
  have hbound : ∀ E, IsCompact E → E ⊆ U →
      ∃ M > 0, ∀ᶠ j in atTop, ∀ y ∈ E, ‖F j y‖ ≤ M := by
    intro E hE hEU
    obtain ⟨M,hM,he⟩ := hest E hE hEU
    refine ⟨‖e.toContinuousLinearMap‖*M+1,by positivity,?_⟩
    filter_upwards [he] with j hj y hy
    have hb' := (hj ⟨y,hEU hy⟩ hy).2
    change ‖e (weightedUnscale (t j) (s.backward (ambientAction U Γ (γ j) y)))‖ ≤ _
    rw [show ambientAction U Γ (γ j) y=(γ j • (⟨y,hEU hy⟩ : U)).val from
      ambientAction_subtype (γ j) ⟨y,hEU hy⟩]
    exact ((e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hb' (norm_nonneg _))).trans (by linarith)
  have htGT : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htp⟩
  have hcoverD : ∀ C : Set (Affine (s.tangentDim+s.normalDim)), IsCompact C →
      C ⊆ connectedComponentIn (e '' O) (e (0,w)) → ∀ᶠ j in atTop, C ⊆ D j := by
    intro C hC hCD
    have hCsub : e.symm '' C ⊆ O := by
      rintro _ ⟨y,hy,rfl⟩
      obtain ⟨z,hz,hzy⟩ := connectedComponentIn_subset (e '' O) (e (0,w)) (hCD hy)
      simpa only [← hzy,e.symm_apply_apply] using hz
    filter_upwards [htGT (hcover (e.symm '' C) (hC.image e.symm.continuous) hCsub)] with j hj y hy
    exact ⟨e.symm y,hj ⟨y,hy,rfl⟩,e.apply_symm_apply y⟩
  have hbaseG : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, G j (e (0,w)) ∈ Subtype.val '' C := by
    refine ⟨K,hK,Eventually.of_forall fun j => ?_⟩
    have he : G j (e (0,w))=(a j).val := by
      change ambientAction U Γ (γ j)⁻¹ (s.forward (weightedScale (t j) (e.symm (e (0,w)))))=_
      rw [e.symm_apply_apply]
      change ambientAction U Γ (γ j)⁻¹ (p j).val=_
      rw [ambientAction_subtype,← hγ j,inv_smul_smul]
    exact ⟨a j,ha j,he.symm⟩
  have hxa : ∀ z ∉ e '' O, ∃ a : ℕ → Affine (s.tangentDim+s.normalDim),
      Tendsto a atTop (𝓝 z) ∧ ∀ᶠ j in atTop, a j ∉ D j := by
    intro z hz
    have hz' : e.symm z ∉ O := fun he => hz ⟨e.symm z,he,e.apply_symm_apply z⟩
    obtain ⟨a,ha,hex⟩ := hexclude (e.symm z) hz' t ht htp
    refine ⟨fun j => e (a j),?_,?_⟩
    · simpa only [e.apply_symm_apply,Function.comp_def] using e.continuous.continuousAt.tendsto.comp ha
    · filter_upwards [hex] with j hj
      rintro ⟨y,hy,he⟩
      exact hj (e.injective he ▸ hy)
  exact cocompact_scaling_biholomorph hconn.isPreconnected hbounded hhol
    (e.toHomeomorph.isOpenMap _ hO) ⟨(0,w),hw,rfl⟩ Aset D
    (fun j => actionLocalSet_subset (γ j) Ω) hAo hDo b F G hbf hbg
    hcoverA hcoverD hbound hbaseG hxa

end NashBoundaryScalingChart
end Release061

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.NashBoundaryScalingChart.global_from_two_sided_oai.{u_1} := @OAI.Release061.NashBoundaryScalingChart.global_from_two_sided_oai.{u_1}
