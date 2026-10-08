-- Prove2me | solution 1 for OAI.Erdos3.CylinderRemovalChain.shell_prefactor_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:22:34.115791+00:00
-- url     : https://prove2.me/submissions/47a4a21f-273b-4d02-a3c0-c995362f3cd8

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem mem_lowDegreeCoordinateSets (b : ℕ) (S : Finset I) :
    S ∈ lowDegreeCoordinateSets I b ↔ S.card ≤ b := by
  simp only [lowDegreeCoordinateSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, hcard⟩
    omega
  · intro h
    exact ⟨S.card, by omega, rfl⟩

theorem lowDegreeCoordinateSets_card (b : ℕ) :
    (lowDegreeCoordinateSets I b).card = ∑ j ∈ Finset.range (b + 1), (Fintype.card I).choose j := by
  rw [lowDegreeCoordinateSets, Finset.card_biUnion]
  · simp only [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

theorem mem_bounded (b : ℕ) (c : ProductCylinder X) :
    c ∈ bounded (X := X) b ↔ c.1.card ≤ b := by
  classical
  simp only [bounded, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mass_mono (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    {f g : (∀ i, X i) → ℝ} (hfg : ∀ x, f x ≤ g x) (c : ProductCylinder X) :
    c.mass μ base f ≤ c.mass μ base g :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => hfg _)

end ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

theorem bounded_card (b : ℕ) :
    (bounded (X := X) b).card =
      ∑ S ∈ lowDegreeCoordinateSets ι b, ∏ i : S, Fintype.card (X i.val) := by
  classical
  have he : bounded (X := X) b =
      (lowDegreeCoordinateSets ι b).sigma (fun S => (Finset.univ : Finset (∀ i : S, X i.val))) := by
    ext c
    simp only [mem_bounded, Finset.mem_sigma, mem_lowDegreeCoordinateSets, Finset.mem_univ, and_true]
  rw [he, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_pi]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_mono {f g : Ω → ℝ} (hfg : ∀ z, f z ≤ g z) (x : ∀ i, X i) :
    observedProductDensity μ p F f x ≤ observedProductDensity μ p F g x := by
  classical
  apply div_le_div_of_nonneg_right _ ((FiniteProbabilityWeights.pi μ).nonneg x)
  apply p.mean_mono
  intro z
  split_ifs
  · exact hfg z
  · exact le_rfl

theorem observedProductDensity_add (f g : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (fun z => f z + g z) x =
      observedProductDensity μ p F f x + observedProductDensity μ p F g x := by
  classical
  have he : p.fiberMean F x (fun z => f z + g z) = p.fiberMean F x f + p.fiberMean F x g := by
    unfold FiniteProbabilityWeights.fiberMean
    rw [← p.mean_add]
    congr 1
    funext z
    split_ifs <;> simp
  change p.fiberMean F x (fun z => f z + g z) / _ = p.fiberMean F x f / _ + p.fiberMean F x g / _
  rw [he, add_div]

theorem observedProductDensity_marginal_le (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (hf : ∀ z, f z ≤ 1) {η : ℝ} {r : ℕ}
    (hbase : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η r)
    (S : Finset ι) (hS : S.card ≤ r) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x ≤ 1 + η := by
  have hm : productConditionalMean μ S (observedProductDensity μ p F f) x ≤
      productConditionalMean μ S (observedProductDensity μ p F (fun _ => 1)) x :=
    (FiniteProbabilityWeights.pi μ).mean_mono
      (fun y => observedProductDensity_mono μ p F hf (productCoordinateMix S x y))
  have hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (x i))).ne'
  have hb := (abs_le.mp (hbase S hS x hx)).2
  linarith

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

theorem cut_add_erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) :
    c.cut F w z + c.erase F w z = w z := by
  unfold cut erase
  split_ifs <;> simp

theorem cut_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.cut F w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.erase F w z := by
  unfold erase
  split_ifs <;> simp [hw]

theorem cut_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.cut F w z ≤ w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.erase F w z ≤ w z := by
  unfold erase
  split_ifs <;> simp [hw]

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem density_cut (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.cut F w) x =
      if c.Contains x then observedProductDensity μ p F w x else 0 := by
  classical
  by_cases hx : c.Contains x
  · rw [if_pos hx]
    change p.fiberMean F x (c.cut F w) / _ = p.fiberMean F x w / _
    congr 1
    unfold FiniteProbabilityWeights.fiberMean
    congr 1
    funext z
    by_cases hz : F z = x
    · simp [cut, hz, hx]
    · simp [hz]
  · rw [if_neg hx]
    have he : p.fiberMean F x (c.cut F w) = 0 := by
      calc
        _ = p.mean (fun _ => 0) := by
          unfold FiniteProbabilityWeights.fiberMean
          congr 1
          funext z
          by_cases hz : F z = x
          · simp [cut, hz, hx]
          · simp [hz]
        _ = 0 := p.mean_const 0
    change p.fiberMean F x (c.cut F w) / _ = 0
    rw [he, zero_div]

theorem density_erase (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.erase F w) x =
      if c.Contains x then 0 else observedProductDensity μ p F w x := by
  classical
  have he : (fun z => c.cut F w z + c.erase F w z) = w := funext (c.cut_add_erase F w)
  have hs := observedProductDensity_add μ p F (c.cut F w) (c.erase F w) x
  rw [he, c.density_cut] at hs
  by_cases hx : c.Contains x
  · rw [if_pos hx] at hs ⊢
    linarith
  · rw [if_neg hx] at hs ⊢
    linarith

theorem mass_erase_self (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.mass μ base (observedProductDensity μ p F (c.erase F w)) = 0 := by
  have hc (y : ∀ i, X i) : c.Contains (productCoordinateMix c.1 (c.assignment base) y) := by
    intro i
    simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property
  change (FiniteProbabilityWeights.pi μ).mean
    (fun y => observedProductDensity μ p F (c.erase F w) (productCoordinateMix c.1 (c.assignment base) y)) = 0
  have he : (fun y => observedProductDensity μ p F (c.erase F w)
      (productCoordinateMix c.1 (c.assignment base) y)) = (fun _ => 0) := by
    funext y
    rw [c.density_erase, if_pos (hc y)]
  rw [he, FiniteProbabilityWeights.mean_const]

omit [∀ i, DecidableEq (X i)] in
theorem mass_erase_le (c d : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    d.mass μ base (observedProductDensity μ p F (c.erase F w)) ≤
      d.mass μ base (observedProductDensity μ p F w) :=
  mass_mono μ base (observedProductDensity_mono μ p F (c.erase_le F w hw)) d

end Erdos3.ProductCylinder

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

theorem mass_cut_self : c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
    c.mass μ base (observedProductDensity μ p F w) := by
  unfold mass productConditionalMean
  congr 1
  funext y
  rw [c.density_cut]
  apply if_pos
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

theorem removedCylinderWeights_length (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (cs : List (ProductCylinder X)) : (removedCylinderWeights F w cs).length = cs.length := by
  induction cs generalizing w with
  | nil => rfl
  | cons c cs ih => simp only [removedCylinderWeights, List.length_cons, ih]

end Erdos3

end

section

namespace Erdos3

open ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

theorem CylinderRemovalChain.mem_mass_gt (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hw : ∀ z, 0 ≤ w z) {d : ProductCylinder X} (hd : d ∈ cs) :
    τ < d.mass μ base (observedProductDensity μ p F w) := by
  revert hw hd
  induction hchain with
  | nil => intro hw hd; simp only [List.not_mem_nil] at hd
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d
      exact hmass
    · exact (ih (c.erase_nonneg F w hw) hd).trans_le (c.mass_erase_le d μ base p F w hw)

theorem CylinderRemovalChain.nodup [∀ i, DecidableEq (X i)]
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hτ : 0 ≤ τ) (hw : ∀ z, 0 ≤ w z) : cs.Nodup := by
  revert hw
  induction hchain with
  | nil => intro _; exact List.nodup_nil
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (c.erase_nonneg F w hw)⟩
    intro hc
    have hm := rest.mem_mass_gt (c.erase_nonneg F w hw) hc
    rw [c.mass_erase_self] at hm
    linarith

end Erdos3

end

section

namespace Erdos3

theorem CylinderRemovalChain.removed_size_mass {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), cf.1.1.card ≤ j ∧
      τ < cf.1.mass μ base (observedProductDensity μ p F cf.2) := by
  induction hchain with
  | nil =>
    intro cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs d hsize hmass hbounded rest ih =>
    intro cf hcf
    change cf ∈ (d, d.cut F w) :: cs.zip (removedCylinderWeights F (d.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      exact ⟨hsize, by rwa [d.mass_cut_self μ base p F w]⟩
    · exact ih cf hcf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem removedCylinderWeights_bounds {Ω ι : Type*} {X : ι → Type*}
    (F : Ω → ∀ i, X i) (w : Ω → ℝ) (cs : List (ProductCylinder X))
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    {f : Ω → ℝ} (hf : f ∈ removedCylinderWeights F w cs) (z : Ω) :
    0 ≤ f z ∧ f z ≤ 1 := by
  induction cs generalizing w with
  | nil => simp only [removedCylinderWeights, List.not_mem_nil] at hf
  | cons c cs ih =>
    change f ∈ c.cut F w :: removedCylinderWeights F (c.erase F w) cs at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨c.cut_nonneg F w hw0 z, (c.cut_le F w hw0 z).trans (hw1 z)⟩
    · exact ih (c.erase F w) (c.erase_nonneg F w hw0)
        (fun x => (c.erase_le F w hw0 x).trans (hw1 x)) hf

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderUniformMass
namespace OAI

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}

omit [∀ i, DecidableEq (X i)] in
theorem CylinderRemovalChain.size_le (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs) :
    ∀ d ∈ cs, d.1.card ≤ j := by
  induction hchain with
  | nil => simp
  | @cons w rem cs d hsize hmass hbounded rest ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hsize
    · exact ih c hc

theorem CylinderRemovalChain.removed_mass_le_two
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    {η : ℝ} (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      cf.1.mass μ base (observedProductDensity μ p F cf.2) ≤ 2 := by
  intro cf hcf
  have hf := removedCylinderWeights_bounds F w cs (fun z => (hw z).1) (fun z => (hw z).2)
    (List.of_mem_zip hcf).2
  have hb := observedProductDensity_marginal_le μ p F hμ cf.2 (fun z => (hf z).2)
    hclose cf.1.1 (hchain.removed_size_mass cf hcf).1 (cf.1.assignment base)
  change productConditionalMean μ cf.1.1 (observedProductDensity μ p F cf.2) (cf.1.assignment base) ≤ 2
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem partial_assignment_card_le_exp {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {V : ℝ} (hV : 0 ≤ V)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (S : Finset ι) {j : ℕ} (hS : S.card ≤ j) :
    (Fintype.card (∀ i : S, X i.val) : ℝ) ≤ Real.exp ((j : ℝ) * V) := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : S, Real.exp V := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hX i.val)
    _ = Real.exp ((S.card : ℝ) * V) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hV)

theorem lowDegreeCoordinateSets_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : ℝ} (hP : 0 ≤ P) (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) (j : ℕ) :
    ((lowDegreeCoordinateSets ι j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + 1)) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (j + 1)) :
      ((Fintype.card ι).choose k : ℝ) ≤ Real.exp ((j : ℝ) * P) := by
    have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
    calc
      _ ≤ (Fintype.card ι : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow (Fintype.card ι) k
      _ ≤ (Real.exp P) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount k
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hP)
  rw [lowDegreeCoordinateSets_card, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ Finset.range (j + 1), Real.exp ((j : ℝ) * P) := Finset.sum_le_sum hterm
    _ = ((j : ℝ) + 1) * Real.exp ((j : ℝ) * P) := by simp
    _ ≤ Real.exp j * Real.exp ((j : ℝ) * P) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem ProductCylinder.bounded_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {P V : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (j : ℕ) :
    ((ProductCylinder.bounded (X := X) j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have he : ((ProductCylinder.bounded (X := X) j).card : ℝ) =
      ∑ S ∈ lowDegreeCoordinateSets ι j, (Fintype.card (∀ i : S, X i.val) : ℝ) := by
    simp only [ProductCylinder.bounded_card, Nat.cast_sum, Fintype.card_pi, Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι j, Real.exp ((j : ℝ) * V) := by
      apply Finset.sum_le_sum
      intro S hS
      exact partial_assignment_card_le_exp hV hX S ((mem_lowDegreeCoordinateSets ι j S).mp hS)
    _ = ((lowDegreeCoordinateSets ι j).card : ℝ) * Real.exp ((j : ℝ) * V) := by simp
    _ ≤ Real.exp ((j : ℝ) * (P + 1)) * Real.exp ((j : ℝ) * V) :=
      mul_le_mul_of_nonneg_right (lowDegreeCoordinateSets_card_le_exp hP hcount j) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem CylinderRemovalChain.length_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ P V : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hτ : 0 ≤ τ) (hw : ∀ z, 0 ≤ w z) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) :
    (cs.length : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have hsub : cs.toFinset ⊆ ProductCylinder.bounded (X := X) j := by
    intro d hd
    exact (ProductCylinder.mem_bounded j d).mpr (hchain.size_le d (List.mem_toFinset.mp hd))
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (hchain.nodup hτ hw)] at hc
  exact (Nat.cast_le.mpr hc).trans (ProductCylinder.bounded_card_le_exp hP hV hcount hX j)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedListError
namespace OAI

section

namespace Erdos3

theorem list_weighted_error_sum {α : Type*} (xs : List α) (P m e : α → ℝ) (C : ℝ)
    (h : ∀ x ∈ xs, P x ≤ C * m x + e x) :
    (xs.map P).sum ≤ C * (xs.map m).sum + (xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CylinderShellCountBudget
namespace OAI

section

namespace Erdos3

theorem uniform_section_norm_product_le_exp {τ L T : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (L + 2 * T + 4) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hM : 3 * τ⁻¹ ≤ Real.exp (T + 2) := by
    rw [Real.exp_add]
    exact (mul_le_mul h3 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hN : 3 * Real.exp (L + T) ≤ Real.exp (L + T + 2) := by
    rw [Real.exp_add (L + T) 2]
    exact (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  calc
    _ ≤ Real.exp (T + 2) * Real.exp (L + T + 2) := mul_le_mul hM hN (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem retained_shell_prefactor_le_exp {m level v τ ε L T : ℝ} {i j : ℕ}
    (_hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hl0 : 0 ≤ level) (hl2 : level ≤ 2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) (hij : i ≤ j) :
    m * level * (v + τ) * (6 + 2 * ε) * (2 : ℝ) ^ i *
      (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (ε + L + 2 * T + j + 10) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  have hbase : m * level * (v + τ) * (6 + 2 * ε) ≤ 16 * (3 + ε) := by
    calc
      _ ≤ 2 * 2 * (1 + 1) * (6 + 2 * ε) := by gcongr
      _ = _ := by ring
  have hconstant : m * level * (v + τ) * (6 + 2 * ε) ≤ Real.exp (ε + 6) := by
    apply hbase.trans
    calc
      _ ≤ Real.exp 4 * Real.exp (ε + 2) :=
        mul_le_mul h16 (by linarith [Real.add_one_le_exp (ε + 2)]) (by linarith) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : (2 : ℝ) ^ i ≤ Real.exp j := by
    calc
      _ ≤ (Real.exp 1) ^ i := pow_le_pow_left₀ (by norm_num) htwo i
      _ = Real.exp i := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr (by exact_mod_cast hij)
  have hn := uniform_section_norm_product_le_exp (L := L) hτ hτinv
  calc
    _ = (m * level * (v + τ) * (6 + 2 * ε)) * (2 : ℝ) ^ i *
        ((3 * τ⁻¹) * (3 * Real.exp (L + T))) := by ring
    _ ≤ Real.exp (ε + 6) * Real.exp j * Real.exp (L + 2 * T + 4) :=
      mul_le_mul (mul_le_mul hconstant hp (by positivity) (Real.exp_pos _).le) hn
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem list_map_sum_le_exp {α : Type*} (xs : List α) (f : α → ℝ) {U V : ℝ}
    (hlen : (xs.length : ℝ) ≤ Real.exp U) (hf : ∀ x ∈ xs, f x ≤ Real.exp V) :
    (xs.map f).sum ≤ Real.exp (U + V) := by
  have hs := list_weighted_error_sum xs f (fun _ => 1) (fun _ => 0) (Real.exp V)
    (fun x hx => by simpa using hf x hx)
  have hs' : (xs.map f).sum ≤ (xs.length : ℝ) * Real.exp V := by
    simpa [mul_comm] using hs
  exact (hs'.trans (mul_le_mul_of_nonneg_right hlen (Real.exp_pos _).le)).trans_eq (Real.exp_add U V).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.shell_prefactor_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P S V level v ε L T : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp S)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp V)
    (hl0 : 0 ≤ level) (hl2 : level ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤
      Real.exp ((j : ℝ) * (P + S + V + 2) + ε + L + 2 * T + 10) := by
  have hlen := hchain.length_le_exp hτ.le (fun z => (hw z).1) hP hS hcount hX
  have hlen' : ((cs.zip (removedCylinderWeights F w cs)).length : ℝ) ≤
      Real.exp ((j : ℝ) * (P + S + 1)) := by
    simpa only [List.length_zip, removedCylinderWeights_length, min_self] using hlen
  have hmass := hchain.removed_mass_le_two hμ hw hη hclose
  have hs := list_map_sum_le_exp (cs.zip (removedCylinderWeights F w cs))
    (fun cf => (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
      (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
        (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))
    (V := (j : ℝ) * V + (ε + L + 2 * T + j + 10)) hlen' (by
      intro cf hcf
      obtain ⟨hsize, hpositive⟩ := hchain.removed_size_mass cf hcf
      have hm0 := (hτ.trans hpositive).le
      have hc := partial_assignment_card_le_exp hV hY cf.1.1 hsize
      have hp := retained_shell_prefactor_le_exp (L := L) hm0 (hmass cf hcf) hl0 hl2 hv0 hv1 hτ hτ1 hε hτinv hsize
      exact (mul_le_mul hc hp (by positivity) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm)
  exact hs.trans_eq (by congr 1; ring)

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.CylinderRemovalChain.shell_prefactor_le_exp.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.CylinderRemovalChain.shell_prefactor_le_exp.{u_1, u_2, u_3, u_4}
