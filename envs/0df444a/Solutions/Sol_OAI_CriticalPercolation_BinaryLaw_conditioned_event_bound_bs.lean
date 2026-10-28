-- Prove2me | solution 1 for OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:08:43.246313+00:00
-- url     : https://prove2.me/submissions/0b60aca1-918e-45a7-bfa1-3e56bb0723ef

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_configuration_entropy_bs
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_inverse_cost_bs
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_reference_density_le_bs

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

omit [Fintype A] in
lemma density_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P] (ω : E → A) :
    density w ω =
      density (fun e : {e // P e} => w e) (fun e => ω e) *
      density (fun e : {e // ¬ P e} => w e) (fun e => ω e) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun e => w e (ω e))).symm

lemma expect_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : (E → A) → ℝ) :
    expect w f =
      expect (fun e : {e // P e} => w e) (fun a =>
        expect (fun e : {e // ¬ P e} => w e) (fun b =>
          f ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b)))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  unfold expect
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have h₁ : (fun i : {e // P e} => e.symm (a, b) i) = a :=
    congrArg Prod.fst (e.apply_symm_apply (a, b))
  have h₂ : (fun i : {e // ¬ P e} => e.symm (a, b) i) = b :=
    congrArg Prod.snd (e.apply_symm_apply (a, b))
  rw [density_split w P, h₁, h₂, mul_assoc]

lemma expect_factor (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : ({e // P e} → A) → ℝ) (g : ({e // ¬ P e} → A) → ℝ) :
    expect w (fun ω => f (fun e => ω e) * g (fun e => ω e)) =
      expect (fun e : {e // P e} => w e) f *
        expect (fun e : {e // ¬ P e} => w e) g := by
  classical
  rw [expect_split w P]
  have h₁ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = a := by
    intro a b
    exact congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  have h₂ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // ¬ P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = b := by
    intro a b
    exact congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  simp_rw [h₁, h₂]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  ring

lemma expect_indep (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (S : Set E) {f g : (E → A) → ℝ}
    (hf : DependsOn f S) (hg : DependsOn g Sᶜ) :
    expect w (fun ω => f ω * g ω) = expect w f * expect w g := by
  classical
  obtain ⟨f', rfl⟩ := dependsOn_iff_exists_comp.mp hf
  obtain ⟨g', rfl⟩ := dependsOn_iff_exists_comp.mp hg
  have hw₁ : ∀ e : S, ∑ a, w e a = 1 := fun e => hw e
  have hw₂ : ∀ e : {e // e ∉ S}, ∑ a, w e a = 1 := fun e => hw e
  have hf' : expect w (fun ω => f' (fun e => ω e)) =
      expect (fun e : S => w e) f' := by
    have h := expect_factor w (fun e => e ∈ S) f' (fun _ => 1)
    simpa only [mul_one, expect_const _ hw₂] using h
  have hg' : expect w (fun ω => g' (fun e => ω e)) =
      expect (fun e : {e // e ∉ S} => w e) g' := by
    have h := expect_factor w (fun e => e ∈ S) (fun _ => 1) g'
    simp only [one_mul, expect_const _ hw₁] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  change expect w (fun ω => f' (fun e => ω e) * g' (fun e => ω e)) =
    expect w (fun ω => f' (fun e => ω e)) * expect w (fun ω => g' (fun e => ω e))
  rw [hf', hg']
  convert expect_factor w (fun e => e ∈ S) f' g' using 1
  all_goals try with_reducible_and_instances rfl
  rfl

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Distribution
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_nonneg {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f := by
  rw [← expect_zero w]
  exact expect_mono hw hf

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

lemma openBond_roots {ω : Set E} {S : Set V} {e : E} (he : e ∈ ω)
    {v w : V} (hv : v ∈ G.ends e) (hw : w ∈ G.ends e)
    (hr : v ∈ roots (G.openGraph ω) S) : w ∈ roots (G.openGraph ω) S := by
  by_cases hvw : v = w
  · simpa [← hvw] using hr
  · have heq : G.ends e = s(v,w) := Sym2.eq_of_ne_mem hvw hv hw (by simp) (by simp)
    exact roots_closed hr ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e, he, heq⟩, hvw⟩)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Divergence
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

lemma mul_log_div_ge_sub {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hs : 0 < p → 0 < r) : p - r ≤ p * Real.log (p / r) := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · simp only [zero_sub, zero_mul]
    exact neg_nonpos.mpr hr
  · have hr := hs hp
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hr hp)) hp.le
    rw [Real.log_div hr.ne' hp.ne'] at h
    rw [Real.log_div hp.ne' hr.ne']
    have he : p * (r / p - 1) = r - p := by field_simp
    rw [he] at h
    nlinarith

lemma mass_sub_le_divergence (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x) - (∑ x, R x) ≤ divergence P R := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => mul_log_div_ge_sub (hP x) (hR x) (hs x)

lemma normalizer_pos (P R : X → ℝ) (_hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    0 < ∑ x, R x * Real.exp (g x) := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun x _ => h x)
    linarith
  exact (mul_pos (hs x hx) (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun y _ => mul_nonneg (hR y) (Real.exp_nonneg _)) (Finset.mem_univ x))

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PushMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma pushMass_nonneg (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (y : Y) :
    0 ≤ pushMass f P y := by
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

lemma pushMass_sum (f : X → Y) (P : X → ℝ) :
    ∑ y, pushMass f P y = ∑ x, P x := by
  classical
  simp only [pushMass]
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
lemma le_pushMass (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (x : X) :
    P x ≤ pushMass f P (f x) := by
  classical
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun z => if f z = f x then P z else 0)
    (fun z _ => by split_ifs <;> simp_all) (Finset.mem_univ x)
  simpa [pushMass] using this

lemma sum_pushMass_mul (f : X → Y) (P : X → ℝ) (g : Y → ℝ) :
    ∑ y, pushMass f P y * g y = ∑ x, P x * g (f x) := by
  classical
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

lemma log_sum_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x)*Real.log ((∑ x, P x)/(∑ x, R x)) ≤ divergence P R := by
  classical
  let A := ∑ x, P x
  let B := ∑ x, R x
  have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => hP x
  rcases eq_or_lt_of_le hA with hA | hA
  · have hz : ∀ x, P x = 0 := by
      intro x
      have hx := Finset.single_le_sum (fun y _ => hP y) (Finset.mem_univ x)
      dsimp [A] at hA
      linarith [hP x]
    simp [hz, divergence]
  have hB : 0 < B := by
    obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
      by_contra! hn
      have ht := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
      exact (not_le_of_gt hA) ht
    exact (hs x hx).trans_le (Finset.single_le_sum (fun y _ => hR y) (Finset.mem_univ x))
  let S : X → ℝ := fun x => R x * (A/B)
  have hS : ∀ x, 0 ≤ S x := fun x => mul_nonneg (hR x) (div_pos hA hB).le
  have hpos : ∀ x, 0 < P x → 0 < S x := fun x hx => mul_pos (hs x hx) (div_pos hA hB)
  have hmass : ∑ x, S x = A := by
    simp only [S, ← Finset.sum_mul]
    change B * (A/B) = A
    field_simp
  have hb := mass_sub_le_divergence P S hP hS hpos
  have he : divergence P S = divergence P R - A*Real.log (A/B) := by
    have ht (x : X) : P x * Real.log (P x / S x) =
        P x * Real.log (P x / R x) - P x * Real.log (A/B) := by
      rcases eq_or_lt_of_le (hP x) with hz | hp
      · simp [← hz]
      · have hr := hs x hp
        simp only [S, Real.log_div hp.ne' (mul_pos hr (div_pos hA hB)).ne',
          Real.log_mul hr.ne' (div_pos hA hB).ne', Real.log_div hp.ne' hr.ne']
        ring
    simp only [divergence, ht, Finset.sum_sub_distrib, ← Finset.sum_mul, A]
  rw [hmass, he] at hb
  change A*Real.log (A/B) ≤ divergence P R
  dsimp [A] at hb ⊢
  linarith

theorem divergence_pushMass_le (f : X → Y) (P R : X → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hR : ∀ x, 0 ≤ R x)
    (hs : ∀ x, 0 < P x → 0 < R x) :
    divergence (pushMass f P) (pushMass f R) ≤ divergence P R := by
  classical
  have hf (y : Y) := log_sum_inequality
    (fun x => if f x = y then P x else 0) (fun x => if f x = y then R x else 0)
    (fun x => by split_ifs <;> simp_all) (fun x => by split_ifs <;> simp_all)
    (fun x hx => by split_ifs at hx ⊢ <;> simp_all)
  have ht (x : X) (y : Y) :
      (if f x = y then P x else 0) *
          Real.log ((if f x = y then P x else 0)/(if f x = y then R x else 0)) =
        if f x = y then P x * Real.log (P x / R x) else 0 := by
    split_ifs <;> simp
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hf y)
  simp only [divergence, ht] at hh
  rw [Finset.sum_comm] at hh
  simpa [pushMass, divergence] using hh

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedEntropy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z I M : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma pushMass_comp (f : X → Y) (g : Y → Z) (P : X → ℝ) :
    pushMass g (pushMass f P) = pushMass (g ∘ f) P := by
  funext z
  have hh := sum_pushMass_mul f P (fun y => if g y = z then (1:ℝ) else 0)
  change (∑ y, if g y = z then pushMass f P y else 0) =
    ∑ x, if g (f x) = z then P x else 0
  simpa only [mul_ite,mul_one,mul_zero] using hh

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma divergence_pushMass_eq (f : X → Y) (P : X → ℝ) (R : Y → ℝ) :
    divergence (pushMass f P) R =
      ∑ x, P x * Real.log (pushMass f P (f x) / R (f x)) :=
  sum_pushMass_mul f P (fun y => Real.log (pushMass f P y / R y))

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]

lemma pushMass_fst (P : X × M → ℝ) (x : X) :
    pushMass Prod.fst P x = ∑ m, P (x,m) := by
  simp only [pushMass,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ReverseReference
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*} [Fintype M]

omit [Fintype M] in
lemma weight_nonneg (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (hk : ∀ i x m, 0 ≤ k i x m) (n : ℕ) (x : X) (m : Fin n → M) :
    0 ≤ weight k u n x m := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hk _ _ _) (ih _ _)

lemma weight_sum_le (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (hk : ∀ i x m, 0 ≤ k i x m) (hs : ∀ i x, ∑ m, k i x m ≤ 1)
    (n : ℕ) (x : X) : ∑ m, weight k u n x m ≤ 1 := by
  classical
  induction n generalizing x with
  | zero => simp [weight]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => M)).sum_comp]
    simp only [Fin.snocEquiv,Equiv.coe_fn_mk,weight,Fin.snoc_last,Fin.init_snoc,Fintype.sum_prod_type]
    calc
      _ = ∑ m, k n x m * ∑ h, weight k u n (u n x m) h := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ m, k n x m := Finset.sum_le_sum fun m _ => by
        simpa using mul_le_mul_of_nonneg_left (ih (u n x m)) (hk n x m)
      _ ≤ 1 := hs n x

section Terminal
variable [Fintype X] {I : Type*} [Fintype I]

omit [Fintype M] [Fintype X] in
lemma terminalWeight_nonneg (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m)
    (x : X) (m : I → M) : 0 ≤ terminalWeight a x m :=
  Finset.prod_nonneg fun i _ => ha i x (m i)

omit [Fintype X] in
lemma terminalWeight_sum (a : I → X → M → ℝ) (ha : ∀ i x, ∑ m, a i x m = 1)
    (x : X) : ∑ m, terminalWeight a x m = 1 := by
  unfold terminalWeight
  rw [← Fintype.prod_sum]
  simp only [ha,Finset.prod_const_one]

omit [Fintype M] [Fintype X] in
lemma joint_nonneg (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m) (n : ℕ) (z) :
    0 ≤ joint μ k u a n z :=
  mul_nonneg (mul_nonneg (hμ _) (weight_nonneg k u hk _ _ _)) (terminalWeight_nonneg a ha _ _)

lemma joint_marginal_le (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (hs : ∀ i x, ∑ m, k i x m ≤ 1)
    (a : I → X → M → ℝ) (ha : ∀ i x, ∑ m, a i x m = 1) (n : ℕ) (x : X) :
    FiniteEntropy.pushMass Prod.fst (joint μ k u a n) x ≤ μ x := by
  rw [FiniteEntropy.pushMass_fst,Fintype.sum_prod_type]
  simp only [joint,← Finset.mul_sum,terminalWeight_sum a ha,mul_one]
  exact (mul_le_mul_of_nonneg_left (weight_sum_le k u hk hs n x) (hμ x)).trans_eq (mul_one _)

end Terminal
end CriticalPercolation.ReverseReference

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Y] [Fintype Z] in
lemma pushMass_at_supported_injection (P : X → ℝ) (e : X → Y)
    (hi : ∀ x x', P x ≠ 0 → P x' ≠ 0 → e x = e x' → x=x')
    (x : X) (hx : P x ≠ 0) : pushMass e P (e x) = P x := by
  unfold pushMass
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    split_ifs with he
    · by_contra hz
      exact hy (hi y x hz hx he)
    · rfl
  · simp

omit [Fintype Z] in
lemma divergence_reference_mono (P R S : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 < P x → 0 < R x) (hRS : ∀ x, R x ≤ S x) :
    divergence P S ≤ divergence P R := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    have hr := hR x hp
    have hs : 0 < S x := hr.trans_le (hRS x)
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hp hs) (div_le_div_of_nonneg_left hp.le hr (hRS x))) (hP x)

theorem mapped_entropy_le (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (e : X → Z) (hi : ∀ x x', P x ≠ 0 → P x' ≠ 0 → e x = e x' → x=x')
    (f : Z → Y) (R : Z → ℝ) (hR : ∀ z, 0 ≤ R z) (μ : Y → ℝ)
    (hμ : ∀ y, pushMass f R y ≤ μ y) (cost : X → ℝ)
    (hd : ∀ x, P x ≤ R (e x) * Real.exp (cost x)) :
    divergence (pushMass (f ∘ e) P) μ ≤ ∑ x, P x * cost x := by
  have hs (x : X) (hx : 0 < P x) : 0 < R (e x) := by
    have he := (hx.trans_le (hd x))
    exact (mul_pos_iff.mp he).resolve_right (fun h => (Real.exp_pos _).not_ge h.2.le) |>.1
  have hs' (z : Z) (hz : 0 < pushMass e P z) : 0 < R z := by
    by_contra! hn
    have ht : pushMass e P z ≤ 0 := by
      unfold pushMass
      apply Finset.sum_nonpos
      intro x _
      split_ifs with he
      · by_contra! hp
        exact (hs x hp).not_ge (he ▸ hn)
      · rfl
    linarith
  have hs'' (y : Y) (hy : 0 < pushMass f (pushMass e P) y) : 0 < pushMass f R y := by
    by_contra! hn
    have ht : pushMass f (pushMass e P) y ≤ 0 := by
      unfold pushMass
      apply Finset.sum_nonpos
      intro z _
      split_ifs with he
      · by_contra! hp
        have hz := (hs' z hp).trans_le (le_pushMass f R hR z)
        rw [he] at hz
        exact hz.not_ge hn
      · rfl
    linarith
  calc
    _ = divergence (pushMass f (pushMass e P)) μ := by rw [pushMass_comp]
    _ ≤ divergence (pushMass f (pushMass e P)) (pushMass f R) :=
      divergence_reference_mono _ _ _ (pushMass_nonneg _ _ (pushMass_nonneg _ _ hP)) hs'' hμ
    _ ≤ divergence (pushMass e P) R := divergence_pushMass_le f _ R
      (pushMass_nonneg _ _ hP) hR hs'
    _ ≤ _ := by
      rw [divergence_pushMass_eq]
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : P x = 0
      · simp [hx]
      · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
        rw [pushMass_at_supported_injection P e hi x hx]
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have hr := hs x hp
        apply (Real.log_le_iff_le_exp (div_pos hp hr)).mpr
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hd x)

end CriticalPercolation.FiniteEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation

namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

lemma compile_valid (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) :
    (compile G order B fuel st stack).Valid st.read := by
  induction fuel generalizing st stack with
  | zero => trivial
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · trivial
    · cases stack with
      | nil => trivial
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest
        · exact ⟨fun he => hd (Or.inr (Or.inl he)), ih _ _, ih _ _⟩

end LazyDFS
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Prob
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (P : Set E → Prop) :
    0 ≤ prob w P := expect_nonneg hp (fun _ => by split_ifs <;> norm_num)

lemma prob_mono (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {P Q : Set E → Prop} (h : ∀ ω, P ω → Q ω) : prob w P ≤ prob w Q := by
  apply expect_mono hp
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
  exact (hQ (h ω hP)).elim

lemma prob_split (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w P = prob w (fun ω => P ω ∧ Q ω) + prob w (fun ω => P ω ∧ ¬Q ω) := by
  unfold prob
  rw [← expect_add]
  congr 1
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

lemma prob_congr (w : E → Prop → ℝ) {P Q : Set E → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : prob w P = prob w Q := by
  congr 1
  funext ω
  exact propext (h ω)

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProbOr
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_diff (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w (fun ω => P ω ∧ ¬Q ω) = prob w P - prob w (fun ω => P ω ∧ Q ω) := by
  have hh := prob_split w P Q
  linarith
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteProductPin
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] [Fintype A] in
lemma pin_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (e : E) (b : A) :
    ∀ j a, 0 ≤ pin w e b j a := by
  intro j a
  by_cases h : j = e
  · subst j; simp [pin]; split_ifs <;> norm_num
  · simpa [pin,h] using hw j a

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Delta
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_eval_indicator (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) : expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  classical
  have ht (ω : E → A) : density w ω * (if ω e = b then 1 else 0) =
      ∏ j, w j (ω j) * (if j = e then if ω j = b then 1 else 0 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [density]
  simp only [expect, ht]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) : (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
      if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp
end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_coordinate_mask (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_pin_eq_force (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (b : Prop) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect w (fun ω => f (Function.update ω e b)) := by
  apply mul_left_cancel₀ hb
  exact (expect_mask_pin w e b f).symm.trans (expect_coordinate_mask w hw e b f)

lemma expect_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect (pin w e a) (fun ω => f (Function.update ω e b)) := by
  rw [expect_pin_eq_force w hw e b hb,expect_pin_eq_force w hw e a ha]
  simp only [Function.update_idem]

lemma prob_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (P : Set E → Prop) :
    prob (pin w e b) P = prob (pin w e a) (fun ω => P (Function.update ω e b)) := by
  exact expect_pin_transport w hw e a b ha hb (fun ω => if P ω then 1 else 0)

lemma delta_eq_pivotal (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    delta w F e = prob (pin w e False)
      (fun ω => F (Function.update ω e True) ∧ ¬F ω) := by
  rw [delta,prob_pin_transport w hw e False True he0 he1]
  have hh := prob_diff (pin w e False)
    (fun ω => F (Function.update ω e True)) F
  have he : prob (pin w e False) (fun ω => F (Function.update ω e True) ∧ F ω) =
      prob (pin w e False) F := by
    apply prob_congr
    intro ω
    constructor
    · exact And.right
    · intro h
      refine ⟨hF _ _ ?_ h,h⟩
      intro j hj
      change Function.update (ω : Set E) e True j
      by_cases hje : j = e
      · subst j; erw [Function.update_self]; trivial
      · erw [Function.update_of_ne hje]; exact hj
  erw [he] at hh
  exact hh.symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma prop_openEdge_reachable (G : BondGraph V E) (ω : Set E)
    {v e t} (he : ω e) (heq : G.ends e = s(v,t)) :
    (G.openGraph ω).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩)

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Variance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_true (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) :
    prob w (fun _ => True) = 1 := by
  simpa only [prob, if_true] using expect_const w hw 1

lemma prob_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : prob w F ≤ 1 := by
  exact (prob_mono w hn (fun _ _ => True.intro)).trans_eq (prob_true w hw)

lemma delta_unit (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    0 ≤ delta w F e ∧ delta w F e ≤ 1 := by
  rw [delta_eq_pivotal w hw e h0 h1 F hF]
  exact ⟨prob_nonneg _ (pin_nonneg w hn e False) _,
    prob_le_one _ (pin_normalized w hw e False) (pin_nonneg w hn e False) _⟩

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CutEdgesSubsetIncident
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical

variable {V E : Type*}

lemma cutEdges_subset_incidentEdges (G : BondGraph V E) (O : Set V) :
    G.cutEdges O ⊆ G.incidentEdges O := by
  rintro e ⟨x,y,he,_,hy⟩
  exact ⟨y,hy,by simp [he]⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ForceClosed
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*}

variable [Fintype E]

omit [Fintype E] in
lemma homogeneous_normalized (w : E → Prop → ℝ) (p : ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e, ∑ b, w e b = 1 := by
  intro e
  simp [Fintype.univ_Prop,h0,h1]

omit [Fintype E] in
lemma homogeneous_positive (w : E → Prop → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e b, 0 < w e b := by
  intro e b
  by_cases hb : b
  · have : b = True := propext (iff_true_intro hb)
    rw [this,h1]; exact hp.1
  · have : b = False := propext (iff_false_intro hb)
    rw [this,h0]; exact sub_pos.mpr hp.2

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryDelta
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma queryDelta_zero_used (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (e : E) (he : e ∈ used) :
    T.queryDelta F w ω e = 0 := by
  induction T generalizing used w with
  | done _ => rfl
  | ask f l r hl hr =>
    have hef : e ≠ f := fun h => hT.1 (h ▸ he)
    simp only [queryDelta,ite_eq_right hef]
    split_ifs
    · exact hr _ hT.2.2 _ (Finset.mem_insert_of_mem he)
    · exact hl _ hT.2.1 _ (Finset.mem_insert_of_mem he)

lemma queryDelta_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) : 0 ≤ T.queryDelta F w ω e := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    simp only [queryDelta]
    split_ifs
    · exact (delta_unit w hw hn f hf0 hf1 F hF).1
    · exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
        (fresh_pin w p used hf f True)
    · exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
        (fresh_pin w p used hf f False)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma clusterObject_cut_closed (ω : Set E) (S : Set V) :
    ∀ e ∈ G.cutEdges (G.clusterObject ω S).1, ¬(G.clusterObject ω S).2 e := by
  rintro e ⟨x,y,he,hx,hy⟩ ⟨hω,_⟩
  exact hx (G.openBond_roots hω (by simp [he] : y ∈ G.ends e)
    (by simp [he] : x ∈ G.ends e) hy)

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma contactWeight_nonneg (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Prop) (e : E) :
    0 ≤ G.contactWeight order B O a p w ω e := by
  unfold contactWeight
  split_ifs
  · apply mul_nonneg hp.1.le
    apply queryDelta_nonneg _ ∅ (LazyDFS.compile_valid G order B _ _ _) hp _ _ w
      (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
      (fun e _ => ⟨h0 e,h1 e⟩)
    rintro s t hst ⟨b,hb,hr⟩
    exact ⟨b,hb,hr.mono (G.openGraph_mono hst)⟩
  · exact le_rfl

lemma contactKernel_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) :
    0 ≤ G.contactKernel order B a p w C ω mark := by
  unfold contactKernel
  by_cases ha : a ∈ C.1
  · rw [ite_eq_left ha]
    split_ifs <;> norm_num
  · rw [ite_eq_right ha]
    cases mark with
    | none => exact le_rfl
    | some e =>
      exact div_nonneg (G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e)
        (prob_nonneg w (fun e b => (homogeneous_positive w hp h0 h1 e b).le) _)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

universe uE

lemma anchors_length {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (anchors d x n h).length = n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [anchors,List.length_append,List.length_singleton,ih]

lemma firstIndex_spec {P : ℕ → Prop} (h : ∃ j, P j) : P (firstIndex P) := by
  rw [firstIndex,dite_eq_left h]
  exact Nat.find_spec h

lemma firstIndex_le {P : ℕ → Prop} {j : ℕ} (hj : P j) : firstIndex P ≤ j := by
  rw [firstIndex,dite_eq_left ⟨j,hj⟩]
  exact Nat.find_min' _ hj

variable {V E : Type*} (G : BondGraph V E)

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma density_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hr₀ : ∀ ω, 0 ≤ r₀ ω) (n : ℕ) (h : History E n)
    (ω : E → Prop) : 0 ≤ density G order d x p w r₀ n h ω := by
  induction n with
  | zero => exact hr₀ ω
  | succ n ih =>
    rw [density]
    split_ifs
    · exact mul_nonneg (ih h.1) (G.contactKernel_nonneg order _ _ hp w h0 h1 _ ω _)
    · exact le_rfl

end Density

section Seed
variable [Fintype V] [Fintype E]

lemma seed_nonneg (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) (ω : E → Prop) : 0 ≤ seed G w u v s ω := by
  unfold seed
  apply mul_nonneg (inv_nonneg.mpr hδ.le)
  split_ifs <;> norm_num

end Seed

section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma kernel_parent_exists (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0) :
    ∃ j, parentPredicate G (anchors d x n h) a ω m j := by
  by_cases ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1
  · have hm : m=none := by
      by_contra hm
      simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
      exact hk rfl
    subst m
    obtain ⟨v,⟨b,hb⟩,hr⟩ := ha
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    exact ⟨j,(v,b),hj,hr.symm⟩
  · cases m with
    | none => simp only [contactKernel,ite_eq_right ha] at hk; exact (hk rfl).elim
    | some e =>
      have he : e ∈ G.cutEdges (G.clusterObject ω (anchorSet d x n h)).1 := by
        by_contra he
        simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
        exact hk rfl
      obtain ⟨u,v,heq,-,z,⟨b,hb⟩,hr⟩ := he
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
      refine ⟨j,(z,b),hj,v,?_,hr⟩
      simp [heq]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma parent_lt_of_exists (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (h : ∃ j, parentPredicate G L a ω m j) : parent G L a ω m < L.length := by
  obtain ⟨z,hz,-⟩ := firstIndex_spec h
  exact (List.getElem?_eq_some_iff.mp hz).1

lemma density_step_support (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)
    (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    density G order d x p w r₀ n h.1 ω ≠ 0 ∧
    G.contactKernel order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
      (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2 ≠ 0 ∧
    side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 := by
  rw [density] at hr
  split_ifs at hr with hs
  · exact ⟨(mul_ne_zero_iff.mp hr).1,(mul_ne_zero_iff.mp hr).2,hs⟩
  · exact (hr rfl).elim

end ExactLaw

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySupport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*} (G : BondGraph V E)

lemma consistent_append (L : List (V × Bool)) (ω : Set E) (hL : Consistent G L ω)
    (a : V) (b : Bool) (hnew : ∀ z ∈ L, (G.openGraph ω).Reachable a z.1 → b=z.2) :
    Consistent G (L++[(a,b)]) ω := by
  intro z hz t ht hr
  rcases List.mem_append.mp hz with hz|hz <;> rcases List.mem_append.mp ht with ht|ht
  · exact hL z hz t ht hr
  · have he := List.mem_singleton.mp ht
    subst t
    exact (hnew z hz hr.symm).symm
  · have he := List.mem_singleton.mp hz
    subst z
    exact hnew t ht hr
  · have he := List.mem_singleton.mp hz
    subst z
    have he := List.mem_singleton.mp ht
    subst t
    rfl

lemma consistent_bases (u v : V) (ω : Set E) (h : ¬(G.openGraph ω).Reachable u v) :
    Consistent G [(u,true),(v,false)] ω := by
  intro z hz t ht hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ht
  rcases hz with rfl|rfl <;> rcases ht with rfl|rfl
  · rfl
  · exact (h hr).elim
  · exact (h hr.symm).elim
  · rfl

section Kernel
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma kernel_colour_consistent (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (z : V × Bool) (hz : z ∈ anchors d x n h) (hr : (G.openGraph ω).Reachable a z.1) :
    side G (anchors d x n h) a ω m = z.2 := by
  have ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1 := ⟨z.1,⟨z.2,hz⟩,hr.symm⟩
  have hm : m=none := by
    by_contra hm
    simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
    exact hk rfl
  subst m
  have hex := kernel_parent_exists G order d x n h a p w ω none hk
  obtain ⟨t,ht,hreach⟩ := firstIndex_spec hex
  have hparent : (anchors d x n h)[parent G (anchors d x n h) a ω none]? = some t := ht
  have hside : side G (anchors d x n h) a ω none = t.2 := by
    simp only [side,hparent,Option.getD_some]
  rw [hside]
  exact hL t (List.mem_of_getElem? ht) z hz (hreach.symm.trans hr)

lemma density_consistent (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (s : ℕ)
    (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    Consistent G (anchors d x n h) ω := by
  induction n with
  | zero =>
    have hE : endpointEvent G (x 0) (x d) s ω := by
      by_contra hE
      simp only [density,seed,ite_eq_right hE,mul_zero] at hr
      exact hr rfl
    exact consistent_bases G _ _ ω hE.1
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w _ n h ω hr
    have hL := ih h.1 hprev
    apply consistent_append G _ ω hL
    intro z hz hzreach
    rw [←hs]
    exact kernel_colour_consistent G order d x n h.1 _ p w ω _ hk hL z hz hzreach

end Kernel

lemma endpoint_labels (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (x (interval d n h).1,true) ∈ anchors d x n h ∧
      (x (interval d n h).2,false) ∈ anchors d x n h := by
  induction n with
  | zero => constructor <;> simp [anchors,interval]
  | succ n ih =>
    have hi := ih h.1
    by_cases ht : (interval d n h.1).2 ≤ (interval d n h.1).1+1
    · constructor
      · exact List.mem_append_left _ (by simpa only [interval,bisect,ite_eq_left ht] using hi.1)
      · exact List.mem_append_left _ (by simpa only [interval,bisect,ite_eq_left ht] using hi.2)
    · cases hb : h.2.1 <;>
        simp only [interval,bisect,hb,Bool.false_eq_true,↓reduceIte,anchors,
          List.mem_append,List.mem_singleton,nextIndex,ite_eq_right ht] <;>
        simp_all only [or_true,true_or,and_self]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AncestryForest
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

namespace Forest
variable (F : Forest)

lemma lineage_base {n : ℕ} (h : n < 2) : F.lineage n = [n] := by
  rw [lineage, dite_eq_left h]

lemma lineage_step {n : ℕ} (h : 2 ≤ n) : F.lineage n = n :: F.lineage (F.parent n) := by
  rw [lineage, dite_eq_right (by omega : ¬n<2)]

lemma self_mem_lineage (n : ℕ) : n ∈ F.lineage n := by
  rw [lineage]
  split_ifs <;> simp

lemma mem_lineage_le {a n : ℕ} (h : a ∈ F.lineage n) : a ≤ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a = n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      exact he.le
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact le_rfl
      · exact (ih (F.parent n) (F.parent_lt n (by omega)) h).trans
          (F.parent_lt n (by omega)).le

lemma root_base {n : ℕ} (h : n < 2) : F.root n = n := by
  rw [root, dite_eq_left h]

lemma root_step {n : ℕ} (h : 2 ≤ n) : F.root n = F.root (F.parent n) := by
  rw [root, dite_eq_right (by omega : ¬n<2)]

lemma root_lt_two (n : ℕ) : F.root n < 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simpa only [F.root_base hn] using hn
    · rw [F.root_step (by omega : 2 ≤ n)]
      exact ih _ (F.parent_lt n (by omega))

lemma root_mem_lineage (n : ℕ) : F.root n ∈ F.lineage n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simp [F.root_base hn,F.lineage_base hn]
    · rw [F.root_step (by omega : 2 ≤ n),F.lineage_step (by omega : 2 ≤ n)]
      exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)))

lemma root_eq_of_mem {a n : ℕ} (h : a ∈ F.lineage n) : F.root a = F.root n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · rfl
      · rw [F.root_step (by omega : 2 ≤ n)]
        exact ih _ (F.parent_lt n (by omega)) h

lemma lineage_subset_of_mem {a n : ℕ} (h : a ∈ F.lineage n) :
    F.lineage a ⊆ F.lineage n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]; exact List.Subset.refl _
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact List.Subset.refl _
      · intro b hb
        rw [F.lineage_step (by omega : 2 ≤ n)]
        exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)) h hb)

lemma parent_mem_lineage {a n : ℕ} (ha : 2 ≤ a) (h : a ∈ F.lineage n) :
    F.parent a ∈ F.lineage n := by
  apply F.lineage_subset_of_mem h
  rw [F.lineage_step ha]
  exact List.mem_cons_of_mem _ (F.self_mem_lineage _)

end Forest
end CriticalPercolation.InterpolationForest

namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

lemma mem_active {u v a : ℕ} : a ∈ F.active u v ↔
    (a ∈ F.lineage u ∨ a ∈ F.lineage v) ∧ 2 ≤ a := by
  simp [active]

lemma active_parent {u v a : ℕ} (ha : a ∈ F.active u v) :
    F.parent a < 2 ∨ F.parent a ∈ F.active u v := by
  by_cases hp : F.parent a < 2
  · exact Or.inl hp
  · apply Or.inr
    rw [mem_active] at ha ⊢
    exact ⟨ha.1.imp (F.parent_mem_lineage ha.2) (F.parent_mem_lineage ha.2),by omega⟩

lemma previous_lineage_le_parent {n a b : ℕ} (ha : a ∈ F.lineage n)
    (hb : b ∈ F.lineage n) (ha2 : 2 ≤ a) (hba : b < a) : b ≤ F.parent a := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · have := F.mem_lineage_le ha
      omega
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · omega
      · exact F.mem_lineage_le hb
      · have := F.mem_lineage_le ha
        have := F.parent_lt b (by omega : 2 ≤ b)
        omega
      · exact ih _ (F.parent_lt n (by omega)) ha hb ha2 hba

theorem previous_active_le_parent {u v a b : ℕ} (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) (hb : b ∈ F.active u v)
    (hside : F.root a = F.root b) (hba : b < a) : b ≤ F.parent a := by
  rw [mem_active] at ha hb
  rcases ha.1 with hau|hav <;> rcases hb.1 with hbu|hbv
  · exact F.previous_lineage_le_parent hau hbu ha.2 hba
  · exact (huv ((F.root_eq_of_mem hau).symm.trans (hside.trans (F.root_eq_of_mem hbv)))).elim
  · exact (huv ((F.root_eq_of_mem hbu).symm.trans (hside.symm.trans (F.root_eq_of_mem hav)))).elim
  · exact F.previous_lineage_le_parent hav hbv ha.2 hba

end CriticalPercolation.InterpolationForest.Forest
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryForest
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma nodeParent_old (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : nodeParent G d x ω (n+1) h i = nodeParent G d x ω n h.1 i := by
  rw [nodeParent,ite_eq_right (by omega : i≠n+2)]

lemma node_old (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : node d x (n+1) h i = node d x n h.1 i := by
  change ((anchors d x n h.1 ++ [_])[i]?).getD _ = _
  rw [List.getElem?_append_left (by simpa only [anchors_length] using hi)]
  rfl

lemma node_current (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1)) :
    node d x (n+1) h (n+2) = (x (nextIndex d n h.1),h.2.1) := by
  unfold node anchors
  rw [List.getElem?_append_right (by simp [anchors_length])]
  simp only [anchors_length,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

lemma node_getElem? (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    (anchors d x n h)[i]? = some (node d x n h i) := by
  have hil : i<(anchors d x n h).length := by simpa only [anchors_length] using hi
  simp only [node,List.getElem?_eq_getElem hil,Option.getD_some]

lemma node_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    node d x n h i ∈ anchors d x n h := List.mem_of_getElem? (node_getElem? d x n h i hi)

lemma node_bases (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    node d x n h 0 = (x 0,true) ∧ node d x n h 1 = (x d,false) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [node_old d x n h 0 (by omega),node_old d x n h 1 (by omega)]
    exact ih h.1

section Support
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_current (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    nodeParent G d x ω (n+1) h (n+2) =
      parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hp := parent_lt_of_exists G _ _ ω _
    (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
  rw [anchors_length] at hp
  simp only [nodeParent,if_true,ite_eq_left hp]

lemma node_colour_parent (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    (node d x n h i).2 = (node d x n h (nodeParent G d x ω n h i)).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i=n+2
    · subst i
      rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr]
      have hp := parent_lt_of_exists G _ _ ω _
        (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
      rw [anchors_length] at hp
      rw [node_old d x n h _ hp]
      rw [← hs]
      simp only [side,node_getElem? d x n h.1 _ hp,Option.getD_some]
    · have hio : i < n+2 := by omega
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 hprev hio

lemma node_root_colour (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hin : i < n+2) :
    (node d x n h i).2 = if (historyForest G d x ω n h).root i = 0 then true else false := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < 2
    · rw [Forest.root_base _ hi]
      have hb := node_bases d x n h
      interval_cases i <;> simp only [hb.1,hb.2,if_true,one_ne_zero,if_false]
    · have hi2 : 2 ≤ i := by omega
      rw [Forest.root_step _ hi2]
      rw [node_colour_parent G order d x p w r₀ n h ω hr i hi2 hin]
      exact ih _ (nodeParent_lt G d x ω n h i hi2)
        ((nodeParent_lt G d x ω n h i hi2).trans hin)

end Support

lemma parent_canonical (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (hex : ∃ i, parentPredicate G L a ω m i) : Canonical G L ω (parent G L a ω m) := by
  intro j z t hj hz ht hr
  have hs := firstIndex_spec hex
  obtain ⟨v,hv,hpred⟩ := hs
  have hvt : v=t := Option.some.inj (hv.symm.trans ht)
  subst v
  have hP : parentPredicate G L a ω m j := by
    refine ⟨z,hz,?_⟩
    cases m with
    | none => exact hpred.trans hr.symm
    | some e =>
      obtain ⟨u,hu,htu⟩ := hpred
      exact ⟨u,hu,hr.trans htu⟩
  have hle := firstIndex_le hP
  exact (Nat.not_le_of_gt hj) hle

lemma canonical_append (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length)
    (hC : Canonical G L ω i) : Canonical G (L++M) ω i := by
  intro j z t hj hz ht
  rw [List.getElem?_append_left (hj.trans hi)] at hz
  rw [List.getElem?_append_left hi] at ht
  exact hC j z t hj hz ht

section CanonicalSupport
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω (nodeParent G d x ω n h i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i = n+2
    · subst i
      rw [nodeParent_current G order d x p w r₀ n h ω hr]
      have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
      apply canonical_append
      · exact parent_lt_of_exists G _ _ ω _ hex
      · exact parent_canonical G _ _ ω _ hex
    · have hio : i < n+2 := by omega
      rw [nodeParent_old G d x ω n h i hio]
      apply canonical_append
      · rw [anchors_length]
        exact (nodeParent_lt G d x ω n h.1 i hi).trans hio
      · exact ih h.1 hprev hio

lemma lineage_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (j : ℕ) (hjn : j < n+2) (hj : Canonical G (anchors d x n h) ω j)
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage j) :
    Canonical G (anchors d x n h) ω i := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj2 : j < 2
    · have he : i=j := by simpa only [Forest.lineage_base _ hj2,List.mem_singleton] using hi
      exact he ▸ hj
    · have hj2' : 2 ≤ j := by omega
      rw [Forest.lineage_step _ hj2',List.mem_cons] at hi
      rcases hi with rfl|hi
      · exact hj
      · exact ih _ (nodeParent_lt G d x ω n h j hj2')
          ((nodeParent_lt G d x ω n h j hj2').trans hjn)
          (nodeParent_canonical G order d x p w r₀ n h ω hr j hj2' hjn) hi

end CanonicalSupport

lemma owner_exists (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    ∃ i, parentPredicate G (anchors d x n h) a ω none i := by
  obtain ⟨b,hb⟩ := ha
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hb
  exact ⟨i,(a,b),hi,.refl _⟩

lemma owner_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    owner G d x n h ω a < n+2 := by
  have hp := parent_lt_of_exists G _ _ ω none (owner_exists G d x n h ω a ha)
  simpa only [anchors_length,owner] using hp

lemma owner_canonical (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    Canonical G (anchors d x n h) ω (owner G d x n h ω a) :=
  parent_canonical G _ _ ω none (owner_exists G d x n h ω a ha)

lemma owner_reachable (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    (G.openGraph ω).Reachable a (node d x n h (owner G d x n h ω a)).1 := by
  obtain ⟨z,hz,hr⟩ := firstIndex_spec (owner_exists G d x n h ω a ha)
  have he : z = node d x n h (owner G d x n h ω a) := Option.some.inj
    (hz.symm.trans (node_getElem? d x n h _ (owner_lt G d x n h ω a ha)))
  exact he ▸ hr

lemma owner_colour (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (b : Bool) (ha : (a,b) ∈ anchors d x n h)
    (hL : Consistent G (anchors d x n h) ω) :
    (node d x n h (owner G d x n h ω a)).2 = b :=
  (hL (a,b) ha _ (node_mem d x n h _ (owner_lt G d x n h ω a ⟨b,ha⟩))
    (owner_reachable G d x n h ω a ⟨b,ha⟩)).symm

section Owners
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma terminal_roots (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
    (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).1)) = 0 ∧
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).2)) = 1 := by
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl := owner_colour G d x n h ω _ true he.1 hL
  have hr' := owner_colour G d x n h ω _ false he.2 hL
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨true,he.1⟩)] at hl
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨false,he.2⟩)] at hr'
  constructor
  · by_contra hz
    simp only [ite_eq_right hz] at hl
    cases hl
  · have hn := (historyForest G d x ω n h).root_lt_two
      (owner G d x n h ω (x (interval d n h).2))
    have hz : (historyForest G d x ω n h).root
        (owner G d x n h ω (x (interval d n h).2)) ≠ 0 := by
      intro hz
      simp only [ite_eq_left hz] at hr'
      cases hr'
    omega

end Owners

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_queryDelta_incident (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (a : V) (e : E)
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v)
    (hq : (compile G order B fuel st stack).queryDelta F w ω e ≠ 0) :
    ∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v := by
  induction fuel generalizing st stack w with
  | zero => exact (hq rfl).elim
  | succ n ih =>
    rw [compile.eq_def] at hq
    dsimp only at hq
    split_ifs at hq with hh
    · exact (hq rfl).elim
    · cases stack with
      | nil => exact (hq rfl).elim
      | cons d rest =>
        dsimp only at hq
        split_ifs at hq with hd
        · exact ih st rest w hst hq
        · have htail : d.1 ∈ st.reached := by
            by_contra ht
            exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht
            exact hd (Or.inr (Or.inr (Or.inr ht)))
          by_cases hef : e=d.2.1
          · subst e
            exact ⟨d.1,by simp [he],hst d.1 htail⟩
          · simp only [queryDelta,ite_eq_right hef] at hq
            by_cases hopen : ω d.2.1
            · rw [ite_eq_left hopen] at hq
              apply ih _ _ _ (fun v hv => ?_) hq
              rcases Finset.mem_insert.mp hv with rfl|hv
              · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
              · exact hst v hv
            · rw [ite_eq_right hopen] at hq
              exact ih (st.closed d.2.1) rest (pin w d.2.1 False) (fun v hv => hst v hv) hq

lemma search_queryDelta_incident [Fintype V] (G : BondGraph V E)
    (order : List (Dart V E)) (B : Set V) (a : V) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E)
    (hq : (search G order a B).queryDelta F w ω e ≠ 0) :
    ∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v := by
  apply compile_queryDelta_incident G order B _ _ _ F w ω a e _ hq
  intro v hv
  have he : v=a := Finset.mem_singleton.mp hv
  subst v
  exact .refl _

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

theorem kernel_contact_geometry (order : List (LazyDFS.Dart V E))
    (S : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (e : E)
    (hk : G.contactKernel order S a p w (G.clusterObject ω S) ω (some e) ≠ 0) :
    a ∉ (G.clusterObject ω S).1 ∧ ¬ω e ∧ ∃ u v,
      G.ends e=s(u,v) ∧ (G.openGraph ω).Reachable a u ∧ v ∈ (G.clusterObject ω S).1 := by
  have ha : a ∉ (G.clusterObject ω S).1 := by
    intro ha
    simp only [contactKernel,ite_eq_left ha,Option.some_ne_none,if_false] at hk
    exact hk rfl
  have he : e ∈ G.cutEdges (G.clusterObject ω S).1 := by
    by_contra he
    simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
    exact hk rfl
  have hc : ¬ω e := fun hoe => G.clusterObject_cut_closed ω S e he
    ⟨hoe,G.cutEdges_subset_incidentEdges _ he⟩
  obtain ⟨u,v,heq,hu,hv⟩ := he
  have hq : (LazyDFS.search G order a S).queryDelta
      (fun σ => ∃ b ∈ S, (G.openGraph σ).Reachable a b) w ω e ≠ 0 := by
    intro hq
    simp only [contactKernel,ite_eq_right ha,contactWeight,hq,mul_zero,ite_self,zero_div] at hk
    exact hk rfl
  obtain ⟨z,hz,hr⟩ := LazyDFS.search_queryDelta_incident G order S a _ w ω e hq
  have hzu : z=u := by
    rw [heq,Sym2.mem_iff] at hz
    rcases hz with rfl|rfl
    · rfl
    · obtain ⟨b,hb,hbv⟩ := hv
      exact (ha ⟨b,hb,hbv.trans hr.symm⟩).elim
  exact ⟨ha,hc,u,v,heq,hzu ▸ hr,hv⟩

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryMarks
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma nodeMark_old (n : ℕ) (h : History E (n+1)) (i : ℕ) (hi : i < n+2) :
    nodeMark (n+1) h i = nodeMark n h.1 i := by
  rw [nodeMark,ite_eq_right (by omega : i ≠ n+2)]

lemma nodeMark_current (n : ℕ) (h : History E (n+1)) : nodeMark (n+1) h (n+2) = h.2.2 := by
  simp only [nodeMark,if_true]

lemma canonical_append_iff (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length) :
    Canonical G (L++M) ω i ↔ Canonical G L ω i := by
  constructor
  · intro hc j z t hj hz ht
    apply hc j z t hj
    · rw [List.getElem?_append_left (hj.trans hi)]
      exact hz
    · rw [List.getElem?_append_left hi]
      exact ht
  · exact canonical_append G L M ω i hi

section Marks
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma current_mark_geometry (n : ℕ) (h : History E (n+1)) (ω : E → Prop) (e : E)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) (hm : h.2.2 = some e) :
    ¬ω e ∧ ∃ u v, G.ends e = s(u,v) ∧
      (G.openGraph ω).Reachable (node d x (n+1) h (n+2)).1 u ∧
      (G.openGraph ω).Reachable (node d x (n+1) h
        (nodeParent G d x ω (n+1) h (n+2))).1 v := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  rw [hm] at hk
  obtain ⟨ha,hclosed,u,v,hev,hau,hv⟩ := kernel_contact_geometry G order _ _ p w ω e hk
  have hex := kernel_parent_exists G order d x n h.1 _ p w ω (some e) hk
  have hp := parent_lt_of_exists G _ _ ω _ hex
  rw [anchors_length] at hp
  rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr,hm,
    node_old d x n h _ hp]
  obtain ⟨z,hz,hpred⟩ := firstIndex_spec hex
  have hnode : z = node d x n h.1 (parent G (anchors d x n h.1)
      (x (nextIndex d n h.1)) ω (some e)) :=
    Option.some.inj (hz.symm.trans (node_getElem? d x n h.1 _ hp))
  rw [hnode] at hpred
  obtain ⟨t,ht,hpt⟩ := hpred
  have htv : t=v := by
    rw [hev,Sym2.mem_iff] at ht
    rcases ht with rfl|rfl
    · have hmemp := node_mem d x n h.1 _ hp
      exact (ha ⟨_,⟨_,hmemp⟩,hpt.trans hau.symm⟩).elim
    · rfl
  exact ⟨hclosed,u,v,hev,hau,htv ▸ hpt⟩

lemma current_canonical_iff (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    Canonical G (anchors d x (n+1) h) ω (n+2) ↔ h.2.2 ≠ none := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
  have hp := parent_lt_of_exists G _ _ ω _ hex
  rw [anchors_length] at hp
  constructor
  · intro hc hm
    obtain ⟨z,hz,hpred⟩ := firstIndex_spec hex
    have ht := node_getElem? d x (n+1) h (n+2) (by omega)
    rw [node_current] at ht
    have hpz : (anchors d x (n+1) h)[parent G (anchors d x n h.1)
        (x (nextIndex d n h.1)) ω h.2.2]? = some z := by
      change ((anchors d x n h.1 ++ [_])[_]?) = some z
      rw [List.getElem?_append_left (by simpa only [anchors_length] using hp)]
      exact hz
    rw [hm] at hpred
    exact hc _ z _ hp hpz ht hpred.symm
  · intro hm
    obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hm
    have hk' := hk
    rw [he] at hk'
    have ha := (kernel_contact_geometry G order _ _ p w ω e hk').1
    intro j z t hj hz ht hrzt
    have ht' := node_getElem? d x (n+1) h (n+2) (by omega)
    rw [node_current] at ht'
    have heqt : t = (x (nextIndex d n h.1),h.2.1) := Option.some.inj (ht.symm.trans ht')
    subst t
    change (anchors d x n h.1 ++ [_])[j]? = some z at hz
    rw [List.getElem?_append_left (by simpa only [anchors_length] using hj)] at hz
    exact ha ⟨z.1,⟨z.2,List.mem_of_getElem? hz⟩,hrzt⟩

lemma canonical_iff_nonhold (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω i ↔ nodeMark n h i ≠ none := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      rw [nodeMark_current]
      exact current_canonical_iff G order d x p w r₀ n h ω hr
    · have hio : i < n+2 := by omega
      rw [nodeMark_old n h i hio]
      change Canonical G (anchors d x n h.1 ++ [_]) ω i ↔ _
      rw [canonical_append_iff G _ _ ω i (by simpa only [anchors_length] using hio)]
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hio

lemma node_mark_geometry (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) (e : E) (hm : nodeMark n h i = some e) :
    ¬ω e ∧ ∃ u v, G.ends e = s(u,v) ∧
      (G.openGraph ω).Reachable (node d x n h i).1 u ∧
      (G.openGraph ω).Reachable (node d x n h (nodeParent G d x ω n h i)).1 v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      rw [nodeMark_current] at hm
      exact current_mark_geometry G order d x p w r₀ n h ω e hr hm
    · have hio : i < n+2 := by omega
      rw [nodeMark_old n h i hio] at hm
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hio hm

end Marks

lemma active_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : i < n+2 := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)

section Active
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma active_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) :
    Canonical G (anchors d x n h) ω i := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
      (owner_canonical G d x n h ω _ ⟨true,he.1⟩) i hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)
      (owner_canonical G d x n h ω _ ⟨false,he.2⟩) i hi

lemma active_nonhold (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : nodeMark n h i ≠ none := by
  have hi2 := (Forest.mem_active _).mp hi |>.2
  exact (canonical_iff_nonhold G order d x p w r₀ n h ω hr i hi2
    (active_lt G d x n h ω i hi)).mp (active_canonical G order d x p w r₀ n h ω hr i hi)

end Active
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryWords
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

lemma interval_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    interval d n (fromWords n b m) = interval d n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fromWords,interval,ih (Fin.init b) (Fin.init m) (Fin.init m')]

lemma nextIndex_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    nextIndex d n (fromWords n b m) = nextIndex d n (fromWords n b m') := by
  simp only [nextIndex,interval_fromWords d n b m m']

lemma anchors_fromWords (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m m' : Fin n → Option E) :
    anchors d x n (fromWords n b m) = anchors d x n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fromWords,anchors,ih (Fin.init b) (Fin.init m) (Fin.init m'),
      nextIndex_fromWords d n (Fin.init b) (Fin.init m) (Fin.init m')]

lemma prefix_self (n : ℕ) (h : History E n) : historyPrefix n h n = h := by
  cases n with
  | zero => cases h; rfl
  | succ n => simp only [historyPrefix,dite_true]

lemma prefix_prev (n : ℕ) (h : History E (n+1)) (k : ℕ) (hk : k ≤ n) :
    historyPrefix (n+1) h k = historyPrefix n h.1 k := by
  rw [historyPrefix,dite_eq_right (by omega : k ≠ n+1)]

lemma prefix_fromWords (n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E)
    (k : ℕ) (hk : k ≤ n) :
    sides k (historyPrefix n (fromWords n b m) k) = sides k (historyPrefix n (fromWords n b m') k) := by
  induction n with
  | zero =>
    have he : k=0 := by omega
    subst k
    exact Subsingleton.elim _ _
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      simp only [prefix_self,sides_fromWords]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev _ _ _ hk',prefix_prev _ _ _ hk']
      exact ih (Fin.init b) (Fin.init m) (Fin.init m') hk'

lemma anchors_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchors d x n h = anchors d x n h' := by
  conv_lhs => rw [←fromWords_sides_marks n h]
  conv_rhs => rw [←fromWords_sides_marks n h']
  rw [hs]
  exact anchors_fromWords d x n _ _ _

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_Mass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.ReverseGuess

lemma step_bound {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) :
    b / (1+s+b)^2 + 1 / (1+s+b) ≤ 1 / (1+s) := by
  have ha : 0 < 1+s := by linarith
  have hab : 0 < 1+s+b := by linarith
  calc
    b / (1+s+b)^2 + 1 / (1+s+b) ≤
        b / ((1+s)*(1+s+b)) + 1 / (1+s+b) := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_left hb (mul_pos ha hab)
      nlinarith
    _ = 1 / (1+s) := by field_simp; ring

end CriticalPercolation.ReverseGuess

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_ReverseGuess
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma reverseMass_eq_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) :
    T.reverseMass p F w ω s = ∑ e, T.reverseGuess p F w ω s e := by
  induction T generalizing used w s with
  | done _ => simp [reverseMass,reverseGuess,queryDelta,prefixScore]
  | ask f l r hl hr =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) /
          (1+s+(b+if e=f then 0 else T'.prefixScore p F w' ω e))^2) =
        b/(1+s+b)^2 + ∑ e, T'.reverseGuess p F w' ω (s+b) e := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) /
          (1+s+(b+if e=f then 0 else T'.prefixScore p F w' ω e))^2 =
          (if e=f then b/(1+s+b)^2 else 0) + T'.reverseGuess p F w' ω (s+b) e := by
        by_cases he : e=f
        · subst e
          simp [reverseGuess,hz,b]
        · simp only [ite_eq_right he,reverseGuess,zero_add]
          congr 2; ring
      simp only [heq,Finset.sum_add_distrib]
      simp
    rw [reverseMass]
    by_cases hf : ω f
    · simp only [ite_eq_left hf]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
      simp only [reverseGuess,queryDelta,prefixScore,ite_eq_left hf]
      rfl
    · simp only [ite_eq_right hf]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]
      simp only [reverseGuess,queryDelta,prefixScore,ite_eq_right hf]
      rfl

lemma reverseMass_bound (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ a b, a ⊆ b → F a → F b) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ T.reverseMass p F w ω s ∧ T.reverseMass p F w ω s ≤ 1/(1+s) := by
  induction T generalizing used w s with
  | done _ => exact ⟨le_rfl, div_nonneg zero_le_one (by linarith)⟩
  | ask f l r hl hr =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    have hb : 0 ≤ b := by
      dsimp [b]
      split_ifs
      · exact mul_nonneg (sub_nonneg.mpr hp.2.le) (delta_unit w hw hn f hf0 hf1 F hF).1
      · exact le_rfl
    have hb' : 0 ≤ b/(1+s+b)^2 := div_nonneg hb (sq_nonneg _)
    have hs' : 0 ≤ s+b := add_nonneg hs hb
    have step {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1/(1+(s+b))) :
        0 ≤ b/(1+s+b)^2+x ∧ b/(1+s+b)^2+x ≤ 1/(1+s) := by
      refine ⟨add_nonneg hb' hx.1, ?_⟩
      calc
        _ ≤ b/(1+s+b)^2 + 1/(1+(s+b)) := add_le_add_right hx.2 _
        _ ≤ _ := by simpa only [add_assoc] using ReverseGuess.step_bound hs hb
    simp only [reverseMass]
    by_cases hbit : ω f
    · simp only [ite_eq_left hbit]
      exact step (hr _ hT.2.2 _ (pin_normalized w hw f True)
        (pin_nonneg w hn f True) (fresh_pin w p used hf f True) hs')
    · simp only [ite_eq_right hbit]
      exact step (hl _ hT.2.1 _ (pin_normalized w hw f False)
        (pin_nonneg w hn f False) (fresh_pin w p used hf f False) hs')

theorem reverseGuess_subprobability (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ a b, a ⊆ b → F a → F b) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) :
    (∀ e, 0 ≤ T.reverseGuess p F w ω 0 e) ∧ (∑ e, T.reverseGuess p F w ω 0 e) ≤ 1 := by
  constructor
  · intro e
    apply div_nonneg _ (sq_nonneg _)
    split_ifs
    · exact mul_nonneg (sub_nonneg.mpr hp.2.le)
        (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
    · exact le_rfl
  · rw [← reverseMass_eq_sum T used hT]
    simpa using (reverseMass_bound T used hT hp F hF w hw hn hf ω (s := 0) le_rfl).2

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BitWeight
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) (e : E) (b : Bool) :
    0 ≤ bitWeight p e b := by cases b <;> simp [bitWeight, hp.1, hp.2]

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Node
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (e : E) (b : Bool) :
    0 < bitWeight p e b := by
  cases b <;> simp [bitWeight, hp.1, hp.2]

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*}

lemma admissible_closed (G : BondGraph V E) (B : Set V) (a b : V) (hb : b ∈ B)
    (ω : E → Bool) (f : E) (h : Admissible G B a b ω f) : ¬configuration ω f := by
  obtain ⟨hn,u,v,hf,hu,hv⟩ := h
  intro hopen
  exact hn ⟨b,hb,hu.trans ((LazyDFS.prop_openEdge_reachable G _ hopen hf).trans hv.symm)⟩

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PrefixScoreNonneg
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*} [Fintype V] [Fintype E]

lemma expect_configuration (w : E → Prop → ℝ) (f : Set E → ℝ) :
    expect (fun e (b : Bool) => w e (b = true)) (fun ω => f (configuration ω)) =
      expect w f := by
  let e : (E → Bool) ≃ (E → Prop) := Equiv.piCongrRight (fun _ => Equiv.propEquivBool.symm)
  have he (ω : E → Bool) : e ω = configuration ω := rfl
  unfold expect
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [he]
  rfl

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryDescriptor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest FiniteEntropy ExactExposure

variable {V E : Type*}

lemma descriptor_sides (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) : sides n h = fun i => (D i).1 := by
  funext i
  exact congrArg (fun D : FixedDescriptor n => (D i).1) hD

lemma sum_history_words [Fintype E] (n : ℕ) (f : History E n → ℝ) :
    (∑ h, f h) = ∑ b : Fin n → Bool, ∑ m : Fin n → Option E, f (fromWords n b m) := by
  rw [← (wordsEquiv (E := E) n).symm.sum_comp f,Fintype.sum_prod_type]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

lemma jointMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (z : (E → Bool) × History E n) : 0 ≤ jointMass G order d x p w s n z := by
  exact mul_nonneg (FiniteProduct.density_nonneg (fun e b => (QueryTree.bitWeight_pos hp e b).le) _)
    (density_nonneg G order d x p w _ hp h0 h1 (seed_nonneg G w _ _ s hδ) n z.2 _)

lemma fixedMass_sum (D : FixedDescriptor n) :
    (∑ z, fixedMass G order d x p w s n D z) = descriptorMass G order d x p w s n D := by
  unfold descriptorMass pushMass
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [sum_history_words]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  symm
  apply (Finset.sum_eq_single (fun i => (D i).1) ?_ ?_).trans
  · apply Finset.sum_congr rfl
    intro m _
    unfold fixedMass
    dsimp only
    split_ifs <;> rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro m _
    have hne : descriptor G d x n (fromWords n b m) (configuration ω) ≠ D := by
      intro he
      have hs := descriptor_sides G d x n _ _ D he
      rw [sides_fromWords] at hs
      exact hb hs
    rw [ite_eq_right hne]
  · simp

lemma conditionedMass_normalized (D : FixedDescriptor n)
    (hD : 0 < descriptorMass G order d x p w s n D) :
    ∑ z, conditionedMass G order d x p w s n D z = 1 := by
  simp only [conditionedMass,← Finset.sum_div,fixedMass_sum,div_self hD.ne']

lemma conditionedMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (D : FixedDescriptor n) (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) : 0 ≤ conditionedMass G order d x p w s n D z := by
  apply div_nonneg _ hD.le
  unfold fixedMass
  dsimp only
  split_ifs
  · exact jointMass_nonneg G order d x p w s n hp h0 h1 hδ _
  · rfl

lemma conditionedMass_support (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0) :
    let h := fromWords n (fun i => (D i).1) z.2
    descriptor G d x n h (configuration z.1) = D ∧
    density G order d x p w (seed G w (x 0) (x d) s) n h (configuration z.1) ≠ 0 := by
  have hf := (div_ne_zero_iff.mp hz).1
  unfold fixedMass at hf
  dsimp only at hf ⊢
  split_ifs at hf with ht
  · exact ⟨ht,(mul_ne_zero_iff.mp hf).2⟩
  · exact (hf rfl).elim

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryRaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma rawContact_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (C : ClusterObject V E) (ω : E → Prop) (mark : Option E) :
    0 ≤ G.rawContact order B a p w C ω mark := by
  unfold rawContact
  split_ifs
  · norm_num
  · norm_num
  · cases mark with
    | none => exact le_rfl
    | some e => exact G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

lemma anchorSet_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchorSet d x n h = anchorSet d x n h' := by
  simp only [anchorSet,anchors_sides d x n h h' hs]

lemma scheduledTargets_eq (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m : Fin n → Option E) (k : ℕ) (hk : k≤n) :
    scheduledTargets (E := E) d x n b k = anchorSet d x k (historyPrefix n (fromWords n b m) k) := by
  rw [scheduledTargets,anchorSet_sides d x k _ _ (prefix_fromWords n b _ m k hk)]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryConfiguration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

lemma scheduleWeight_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (n : ℕ) (b : Fin n → Bool) (i : Fin n)
    (ω : E → Prop) (m : Option E) : 0 ≤ scheduleWeight G order d x p w n b i ω m :=
  G.rawContact_nonneg order _ _ hp w h0 h1 _ ω m

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryParents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

lemma parent_eq_previous (u v a : ℕ) (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) :
    F.parent a = ((Finset.range a).filter fun b =>
      (b<2 ∨ b ∈ F.active u v) ∧ F.root b = F.root a).sup id := by
  have ha2 := (F.mem_active.mp ha).2
  apply le_antisymm
  · apply Finset.le_sup (f := id)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (F.parent_lt a ha2),
      F.active_parent ha,(F.root_step ha2).symm⟩
  · apply Finset.sup_le
    intro b hb
    obtain ⟨hba,hb,hroot⟩ := Finset.mem_filter.mp hb
    have hba' := Finset.mem_range.mp hba
    rcases hb with hb|hb
    · have hr := F.mem_lineage_le (F.root_mem_lineage (F.parent a))
      rw [← F.root_step ha2,← hroot,F.root_base hb] at hr
      exact hr
    · exact F.previous_active_le_parent huv ha hb hroot.symm hba'
end CriticalPercolation.InterpolationForest.Forest

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

lemma activeNodes_eq_descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) :
    activeNodes G d x n h ω = descriptorActive n D := by
  ext i
  constructor
  · intro hi
    have hi2 := (Forest.mem_active _).mp hi |>.2
    have hin := active_lt G d x n h ω i hi
    let j : Fin n := ⟨i-2,by omega⟩
    have hj : j.val+2=i := by dsimp [j]; omega
    refine Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hj⟩
    rw [← hD]
    simpa only [descriptor,hj,decide_eq_true_eq] using hi
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have ht := (Finset.mem_filter.mp hj).2
    rw [← hD] at ht
    simpa only [descriptor,decide_eq_true_eq] using ht

lemma node_eq_descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) (i : ℕ) :
    node d x n h i = descriptorNode (E := E) d x n D i := by
  have hs := descriptor_sides G d x n h ω D hD
  unfold node descriptorNode
  rw [anchors_sides d x n h (fromWords n (fun j => (D j).1) (fun _ => (none : Option E)))
    (hs.trans (sides_fromWords n _ _).symm)]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
variable (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0)

include hr in
lemma node_colour_eq_iff_root (i j : ℕ) (hi : i<n+2) (hj : j<n+2) :
    (node d x n h i).2 = (node d x n h j).2 ↔
      (historyForest G d x ω n h).root i = (historyForest G d x ω n h).root j := by
  rw [node_root_colour G order d x p w _ n h ω hr i hi,
    node_root_colour G order d x p w _ n h ω hr j hj]
  have hi2 := (historyForest G d x ω n h).root_lt_two i
  have hj2 := (historyForest G d x ω n h).root_lt_two j
  split_ifs <;> simp_all <;> omega

include hr in

theorem active_parent_eq_descriptor (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) (i : ℕ)
    (hi : i ∈ activeNodes G d x n h ω) :
    nodeParent G d x ω n h i = descriptorParent (E := E) d x n D i := by
  have ht := terminal_roots G order d x p w s n h ω hr
  have hne : (historyForest G d x ω n h).root
      (owner G d x n h ω (x (interval d n h).1)) ≠
      (historyForest G d x ω n h).root
      (owner G d x n h ω (x (interval d n h).2)) := by rw [ht.1,ht.2]; omega
  have he := (historyForest G d x ω n h).parent_eq_previous _ _ i hne hi
  change nodeParent G d x ω n h i = _ at he
  rw [he]
  unfold descriptorParent
  congr 1
  ext j
  simp only [Finset.mem_filter]
  by_cases hj : j ∈ Finset.range i
  · simp only [hj,true_and]
    have hji := Finset.mem_range.mp hj
    have hin := active_lt G d x n h ω i hi
    rw [← activeNodes_eq_descriptor G d x n h ω D hD,
      ← node_eq_descriptor G d x n h ω D hD j,← node_eq_descriptor G d x n h ω D hD i]
    exact and_congr_right fun _ => (node_colour_eq_iff_root G order d x p w s n h ω hr j i
      (hji.trans hin) hin).symm
  · simp only [hj,false_and]

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySwitches
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph SearchTree BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma switched_mono (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ) :
    ω ⊆ switched n h ω S := fun _ he => Or.inl he

lemma canonical_misses_targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (i : ℕ) (hin : i < n+2) (hc : Canonical G (anchors d x n h) ω i) :
    ¬∃ b ∈ targets d x n h i, (G.openGraph ω).Reachable (node d x n h i).1 b := by
  rintro ⟨b,⟨j,hji,hjb⟩,hr⟩
  exact hc j _ _ hji (node_getElem? d x n h j (hji.trans hin))
    (node_getElem? d x n h i hin) (hjb ▸ hr.symm)

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryPrefix
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

lemma anchors_prefix_getElem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < k+2) :
    (anchors d x k (historyPrefix n h k))[i]? = (anchors d x n h)[i]? := by
  induction n with
  | zero => have he : k=0 := by omega
            subst k
            rw [prefix_self]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; rw [prefix_self]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev n h k hk',ih h.1 hk']
      change _ = (anchors d x n h.1 ++ [_])[i]?
      rw [List.getElem?_append_left (by rw [anchors_length]; omega)]

lemma node_prefix (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < k+2) :
    node d x k (historyPrefix n h k) i = node d x n h i := by
  simp only [node,anchors_prefix_getElem d x n h k hk i hi]

lemma marks_nodeMark (n : ℕ) (h : History E n) (i : Fin n) :
    marks n h i = nodeMark n h (i.val+2) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [marks,Fin.snoc_last,Fin.val_last,nodeMark_current]
    · rw [marks,Fin.snoc_castSucc,ih h.1 j,nodeMark_old n h _ (by simp)]
      rfl

lemma targets_prefix (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) :
    targets d x n h (k+2) = anchorSet d x k (historyPrefix n h k) := by
  ext v
  constructor
  · rintro ⟨j,hj,hjv⟩
    refine ⟨(node d x k (historyPrefix n h k) j).2,?_⟩
    have hm := node_mem d x k (historyPrefix n h k) j hj
    rw [node_prefix d x n h k hk j hj] at hm ⊢
    have heq : node d x n h j = (v, (node d x n h j).2) := Prod.ext hjv rfl
    rw [← heq]
    exact hm
  · rintro ⟨b,hb⟩
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    have hjlt : j < k+2 := by
      have ht := List.getElem?_eq_some_iff.mp hj
      simpa only [anchors_length] using ht.1
    have hnode : node d x k (historyPrefix n h k) j = (v,b) := by
      simp only [node,hj,Option.getD_some]
    exact ⟨j,hjlt,congrArg Prod.fst ((node_prefix d x n h k hk j hjlt).symm.trans hnode)⟩

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryCosts
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

lemma descriptorParent_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n)
    (i : ℕ) (hi : 0 < i) : descriptorParent (E := E) d x n D i < i := by
  unfold descriptorParent
  exact (Finset.sup_lt_iff hi).mpr (fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1)

lemma scheduledTargets_nodes (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    scheduledTargets (E := E) d x n (fun j => (D j).1) i.val =
      {v | ∃ j < i.val+2, (descriptorNode (E := E) d x n D j).1=v} :=
  (targets_prefix d x n _ i.val i.isLt.le).symm

lemma scheduled_parent_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val+2))).1 ∈
      scheduledTargets (E := E) d x n (fun j => (D j).1) i.val := by
  rw [scheduledTargets_nodes]
  exact ⟨_,descriptorParent_lt d x n D _ (by omega),rfl⟩

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_active_admissible (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0)
    (i : ActiveIndex n D) :
    ∃ e, m i.val = some e ∧ Admissible G
      (scheduledTargets (E := E) d x n (fun j => (D j).1) i.val.val)
      (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i) ω e := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hi : i.val.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,rfl⟩
  have hn := active_nonhold G order d x p w _ n h _ hr _ hi
  obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hn
  refine ⟨e,?_,?_⟩
  · have hm := marks_nodeMark n h i.val
    rw [marks_fromWords] at hm
    exact hm.trans he
  · have hc := active_canonical G order d x p w _ n h _ hr _ hi
    have hmiss := canonical_misses_targets G d x n h _ _ (by have := i.val.isLt; omega) hc
    obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w _ n h _ hr _ (by omega)
      (by have := i.val.isLt; omega) e he
    have hl : (node d x n h (i.val.val+2)).1 = activeLeft (E := E) d x n D i :=
      congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
    have hr' : (node d x n h (nodeParent G d x (configuration ω) n h (i.val.val+2))).1 =
        activeRight (E := E) d x n D i := by
      rw [active_parent_eq_descriptor G order d x p w s n h _ hr D hD _ hi]
      exact congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
    have ht : targets d x n h (i.val.val+2) =
        scheduledTargets (E := E) d x n (fun j => (D j).1) i.val.val := by
      rw [targets_prefix d x n h _ i.val.isLt.le,scheduledTargets_eq d x n _ m _ i.val.isLt.le]
    rw [hl,ht] at hmiss
    exact ⟨hmiss,u,v,hev,hl ▸ hu,hr' ▸ hv⟩

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedBits
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.MarkedBits
open scoped Classical
open FiniteProduct ExactExposure

variable {E I : Type*}

variable [Fintype I]

lemma masked_join (S : Finset I) (m : I → Option E) (i : I) :
    (if i ∈ S then masked S m i else masked Sᶜ m i) = m i := by
  simp only [masked,Finset.mem_compl]
  split_ifs <;> rfl

lemma masked_injective (S : Finset I) (m m' : I → Option E)
    (h1 : masked S m = masked S m') (h2 : masked Sᶜ m = masked Sᶜ m') : m=m' := by
  funext i
  rw [← masked_join S m i,← masked_join S m' i,h1,h2]

omit [Fintype I] in

lemma opened_injective_closed (S : Finset I) (m : I → Option E) (ω η : E → Bool)
    (hω : ∀ i ∈ S, ∀ e, m i = some e → ω e = false)
    (hη : ∀ i ∈ S, ∀ e, m i = some e → η e = false)
    (he : opened S m ω = opened S m η) : ω=η := by
  funext e
  by_cases hm : ∃ i ∈ S, m i = some e
  · obtain ⟨i,hi,him⟩ := hm
    rw [hω i hi e him,hη i hi e him]
  · have hh := congrFun he e
    simpa only [opened,ite_eq_right hm] using hh

end CriticalPercolation.MarkedBits

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReverseKernels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.kernelsFinDec
lemma pivotGuess_subprobability (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) :
    (∀ e, 0 ≤ pivotGuess G order d x p w n D i ω e) ∧
      (∑ e, pivotGuess G order d x p w n D i ω e) ≤ 1 := by
  apply SearchTree.reverseGuess_subprobability _ ∅ (LazyDFS.compile_valid G order _ _ _ _) hp
  · rintro a b hab ⟨v,hv,hr⟩
    exact ⟨v,hv,hr.mono (G.openGraph_mono hab)⟩
  · exact homogeneous_normalized w p h0 h1
  · exact fun e b => (homogeneous_positive w hp h0 h1 e b).le
  · exact fun e _ => ⟨h0 e,h1 e⟩

lemma inverseKernel_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (j : ℕ) (ω : E → Bool) (m : Option E) : 0 ≤ inverseKernel G order d x p w n D j ω m := by
  unfold inverseKernel
  split_ifs with hj hi hm hm
  · cases m with
    | none => exact le_rfl
    | some e => exact (pivotGuess_subprobability G order d x p w n D hp h0 h1 _ ω).1 e
  · exact zero_le_one
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl

lemma inverseKernel_sum (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (j : ℕ) (ω : E → Bool) : (∑ m, inverseKernel G order d x p w n D j ω m) ≤ 1 := by
  unfold inverseKernel
  split_ifs with hj hi
  · rw [Fintype.sum_option]
    simp only [zero_add]
    exact (pivotGuess_subprobability G order d x p w n D hp h0 h1 _ ω).2
  · simp
  · simp

lemma contactTotal_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) :
    0 ≤ contactTotal G order d x p w n D i ω :=
  Finset.sum_nonneg fun m _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m

lemma inactiveKernel_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (i : Fin n) (ω : E → Bool) (m : Option E) : 0 ≤ inactiveKernel G order d x p w n D i ω m := by
  unfold inactiveKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m)
      (contactTotal_nonneg G order d x p w n D hp h0 h1 i ω)

lemma inactiveKernel_sum (i : Fin n) (ω : E → Bool) :
    (∑ m, inactiveKernel G order d x p w n D i ω m) = 1 := by
  unfold inactiveKernel
  split_ifs with hi ht
  · simp
  · simp
  · rw [← Finset.sum_div]
    exact div_self ht

lemma inverseReference_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (z) :
    0 ≤ inverseReference G order d x p w n D z :=
  ReverseReference.joint_nonneg _ (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    _ _ (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    _ (inactiveKernel_nonneg G order d x p w n D hp h0 h1) n z

lemma inverseReference_marginal (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Bool) :
    pushMass Prod.fst (inverseReference G order d x p w n D) ω ≤
      FiniteProduct.density (QueryTree.bitWeight p) ω := by
  have he := ReverseReference.joint_marginal_le
    (FiniteProduct.density (QueryTree.bitWeight p) : (E → Bool) → ℝ)
    (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D)
    (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    (inverseKernel_sum G order d x p w n D hp h0 h1)
    (inactiveKernel G order d x p w n D) (inactiveKernel_sum G order d x p w n D) n ω
  refine Eq.trans_le ?_ he
  unfold pushMass
  apply Finset.sum_congr
  · ext z
    simp only [Finset.mem_univ]
  · intro z _
    rfl

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryOutput
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph LazyDFS BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma hasSide_mono_reachable (L : List (V × Bool)) (ω : Set E) (b : Bool) {u v : V}
    (hu : HasSide G L ω b u) (hr : (G.openGraph ω).Reachable u v) :
    HasSide G L ω b v := by
  obtain ⟨z,hz,hb,hrz⟩ := hu
  exact ⟨z,hz,hb,hrz.trans hr⟩

lemma hasSide_unique (L : List (V × Bool)) (ω : Set E) (hL : Consistent G L ω)
    {b c : Bool} {v : V} (hb : HasSide G L ω b v) (hc : HasSide G L ω c v) : b=c := by
  obtain ⟨z,hz,hzb,hzv⟩ := hb
  obtain ⟨t,ht,htc,htv⟩ := hc
  exact hzb.symm.trans ((hL z hz t ht (hzv.trans htv.symm)).trans htc)

section Output
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma switched_side_adj (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) {b : Bool} {u v : V}
    (hu : HasSide G (anchors d x n h) ω b u)
    (huv : (G.openGraph (switched n h ω S)).Adj u v) :
    HasSide G (anchors d x n h) ω b v := by
  obtain ⟨⟨e,he,hev⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
  rcases he with he|⟨i,hi,him⟩
  · exact hasSide_mono_reachable G _ ω b hu (prop_openEdge_reachable G ω he hev)
  · obtain ⟨_,a,c,heac,ha,hc⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i
      (hS i hi).1 (hS i hi).2 e him
    have hip := nodeParent_lt G d x ω n h i (hS i hi).1
    have hcol := node_colour_parent G order d x p w r₀ n h ω hr i (hS i hi).1 (hS i hi).2
    have hA : HasSide G (anchors d x n h) ω (node d x n h i).2 a :=
      ⟨_,node_mem d x n h i (hS i hi).2,rfl,ha⟩
    have hC : HasSide G (anchors d x n h) ω (node d x n h i).2 c :=
      ⟨_,node_mem d x n h _ (hip.trans (hS i hi).2),hcol.symm,hc⟩
    rcases Sym2.eq_iff.mp (hev.symm.trans heac) with ⟨hua,hvc⟩|⟨huc,hva⟩
    · subst u; subst v
      exact (hasSide_unique G _ ω hL hu hA).symm ▸ hC
    · subst u; subst v
      exact (hasSide_unique G _ ω hL hu hC).symm ▸ hA

lemma switched_side_reachable (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) {b : Bool} {u v : V}
    (hu : HasSide G (anchors d x n h) ω b u)
    (huv : (G.openGraph (switched n h ω S)).Reachable u v) :
    HasSide G (anchors d x n h) ω b v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact hu
  | tail _ hstep ih => exact switched_side_adj G order d x p w r₀ n h ω hr hL S hS ih hstep

theorem switched_terminal_distinct (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) :
    ¬(G.openGraph (switched n h ω S)).Reachable
      (x (interval d n h).1) (x (interval d n h).2) := by
  intro hreach
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl : HasSide G (anchors d x n h) ω true (x (interval d n h).1) :=
    ⟨_,he.1,rfl,.refl _⟩
  have hr' : HasSide G (anchors d x n h) ω false (x (interval d n h).2) :=
    ⟨_,he.2,rfl,.refl _⟩
  have hh := switched_side_reachable G order d x p w _ n h ω hr hL S hS hl hreach
  cases hasSide_unique G _ ω hL hh hr'

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma active_index_bounds (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E) :
    ∀ i ∈ activeNodes G d x n h ω, 2 ≤ i ∧ i < n+2 := by
  intro i hi
  exact ⟨((historyForest G d x ω n h).mem_active.mp hi).2,active_lt G d x n h ω i hi⟩

lemma active_lineage_reachable (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (u : ℕ) (hu : u = owner G d x n h ω (x (interval d n h).1) ∨
      u = owner G d x n h ω (x (interval d n h).2))
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage u) (hin : i < n+2) :
    (G.openGraph (switched n h ω (activeNodes G d x n h ω))).Reachable
      (node d x n h i).1 (node d x n h ((historyForest G d x ω n h).root i)).1 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hib : i < 2
    · rw [Forest.root_base _ hib]
    · have hi2 : 2 ≤ i := by omega
      have hia : i ∈ activeNodes G d x n h ω := by
        apply (Forest.mem_active _).mpr
        exact ⟨hu.elim (fun e => Or.inl (e ▸ hi)) (fun e => Or.inr (e ▸ hi)),hi2⟩
      have hm := active_nonhold G order d x p w r₀ n h ω hr i hia
      obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hm
      obtain ⟨_,a,b,heab,ha,hb⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi2 hin e he
      have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
      have heopen : switched n h ω (activeNodes G d x n h ω) e := Or.inr ⟨i,hia,he⟩
      have hparent := (ha.mono hmon).trans
        ((prop_openEdge_reachable G _ heopen heab).trans (hb.symm.mono hmon))
      rw [Forest.root_step _ hi2]
      exact hparent.trans (ih _ (nodeParent_lt G d x ω n h i hi2)
        ((historyForest G d x ω n h).parent_mem_lineage hi2 hi)
        ((nodeParent_lt G d x ω n h i hi2).trans hin))

theorem switched_terminal_bases (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    let η := switched n h ω (activeNodes G d x n h ω)
    (G.openGraph η).Reachable (x (interval d n h).1) (x 0) ∧
    (G.openGraph η).Reachable (x (interval d n h).2) (x d) := by
  have he := endpoint_labels d x n h
  have hrts := terminal_roots G order d x p w s n h ω hr
  have hb := node_bases d x n h
  have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
  constructor
  · have hanc := active_lineage_reachable G order d x p w _ n h ω hr _ (Or.inl rfl) _
      ((historyForest G d x ω n h).self_mem_lineage _) (owner_lt G d x n h ω _ ⟨true,he.1⟩)
    rw [hrts.1,hb.1] at hanc
    exact ((owner_reachable G d x n h ω _ ⟨true,he.1⟩).mono hmon).trans hanc
  · have hanc := active_lineage_reachable G order d x p w _ n h ω hr _ (Or.inr rfl) _
      ((historyForest G d x ω n h).self_mem_lineage _) (owner_lt G d x n h ω _ ⟨false,he.2⟩)
    rw [hrts.2,hb.2] at hanc
    exact ((owner_reachable G d x n h ω _ ⟨false,he.2⟩).mono hmon).trans hanc

lemma density_seed_support (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) : r₀ ω ≠ 0 := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1

theorem switched_endpointEvent (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    endpointEvent G (x (interval d n h).1) (x (interval d n h).2) s
      (switched n h ω (activeNodes G d x n h ω)) := by
  have hseed := density_seed_support G order d x p w _ n h ω hr
  have ho : endpointEvent G (x 0) (x d) s ω := by
    by_contra ho
    simp only [seed,ite_eq_right ho,mul_zero] at hseed
    exact hseed rfl
  have hb := switched_terminal_bases G order d x p w s n h ω hr
  have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
  refine ⟨switched_terminal_distinct G order d x p w s n h ω hr _
    (active_index_bounds G d x n h ω),?_,?_⟩
  · apply ho.2.1.trans
    apply Finset.card_le_card
    intro v hv
    have hv' : (G.openGraph ω).Reachable (x 0) v := (Set.mem_toFinset (s := G.cluster ω (x 0)) (a := v)).mp hv
    exact (Set.mem_toFinset (s := G.cluster (switched n h ω (activeNodes G d x n h ω)) (x (interval d n h).1)) (a := v)).mpr (hb.1.trans (hv'.mono hmon))
  · apply ho.2.2.trans
    apply Finset.card_le_card
    intro v hv
    have hv' : (G.openGraph ω).Reachable (x d) v := (Set.mem_toFinset (s := G.cluster ω (x d)) (a := v)).mp hv
    exact (Set.mem_toFinset (s := G.cluster (switched n h ω (activeNodes G d x n h ω)) (x (interval d n h).2)) (a := v)).mpr (hb.2.trans (hv'.mono hmon))

end Output
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryStages
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*}

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.stagesFinDec
lemma stage_last (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E) :
    stage n D ω m n = opened (activeSteps n D) m ω := by
  unfold stage stageIndices
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]

lemma configuration_opened (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E)
    (S : Finset (Fin n)) :
    configuration (opened S m ω) = switched n (fromWords n (fun j => (D j).1) m)
      (configuration ω) (S.image fun i => i.val+2) := by
  apply Set.ext
  intro e
  have hm (i : Fin n) : nodeMark n (fromWords n (fun j => (D j).1) m) (i.val+2) = m i := by
    rw [← marks_nodeMark,marks_fromWords]
  simp only [configuration,MarkedBits.opened,switched,Set.mem_ofPred_eq]
  simp only [Finset.mem_image,exists_exists_and_eq_and,hm]
  by_cases he : ∃ i ∈ S, m i = some e
  · simp only [he,if_true,or_true]
  · simp only [he,if_false,or_false]
    rfl

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_mark_closed (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) : ω e = false := by
  obtain ⟨f,hf,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hfe : f=e := Option.some.inj (hf.symm.trans he)
  subst f
  have hc := admissible_closed G _ _ _ (scheduled_parent_mem d x n D i) ω e ha
  exact Bool.eq_false_iff.mpr hc

lemma supported_opening_injective
    (z z' : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0)
    (hz' : conditionedMass G order d x p w s n D z' ≠ 0)
    (he : (stage n D z.1 z.2 n,masked (activeSteps n D) z.2,masked (activeSteps n D)ᶜ z.2) =
      (stage n D z'.1 z'.2 n,masked (activeSteps n D) z'.2,masked (activeSteps n D)ᶜ z'.2)) : z=z' := by
  rcases z with ⟨ω,m⟩
  rcases z' with ⟨η,m'⟩
  have hm : m=m' := masked_injective (activeSteps n D) m m'
    (congrArg (fun y => y.2.1) he) (congrArg (fun y => y.2.2) he)
  subst m'
  have ho := congrArg Prod.fst he
  simp only [stage_last] at ho
  exact Prod.ext (opened_injective_closed _ m ω η
    (supported_mark_closed G order d x p w s n D ω m hz)
    (supported_mark_closed G order d x p w s n D η m hz') ho) rfl

lemma stage_endpointEvent (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) :
    endpointEvent G
      (x (interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))).1)
      (x (interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))).2) s
      (configuration (stage n D ω m n)) := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  rw [stage_last,configuration_opened]
  have he := switched_endpointEvent G order d x p w s n (fromWords n (fun j => (D j).1) m) _ hr
  rw [activeNodes_eq_descriptor G d x n _ _ D hD] at he
  rw [interval_fromWords d n _ m (fun _ => none)] at he
  exact he

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryOutputEntropy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.outputEntropyFinDec
lemma inverseLog_expectation (Q : ((E → Bool) × (Fin n → Option E)) → ℝ) :
    (∑ z, Q z * inverseLog G order d x p w n D z.1 z.2) =
      2*(∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) +
      ∑ z, Q z * logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration z.1) := by
  simp only [inverseLog,mul_add,Finset.sum_add_distrib]
  congr 1
  simp_rw [mul_left_comm (Q _) 2,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem conditioned_output_entropy (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    divergence (outputMass G order d x p w s n D) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
      (4*(16/(2*p*(1-p)))+6)*constructionCost G order d x p w c s n D +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 := by
  let Q := conditionedMass G order d x p w s n D
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  let L := constructionCost G order d x p w c s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hm := mapped_entropy_le Q hQ (recorded n D)
    (fun z z' hz hz' he => supported_opening_injective G order d x p w s n D z z' hz hz' he)
    Prod.fst (inverseReference G order d x p w n D)
    (inverseReference_nonneg G order d x p w n D hp h0 h1) μ
    (inverseReference_marginal G order d x p w n D hp h0 h1)
    (fun z => L+inverseLog G order d x p w n D z.1 z.2)
    (conditioned_reference_density_le_bs G order d x p w n D s hd hp h0 h1 hc hc1 hconn hδ hD)
  have he : (∑ z, Q z*(L+inverseLog G order d x p w n D z.1 z.2)) =
      L + (2*(∑ i ∈ activeSteps n D, ∑ z, Q z*Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) +
      ∑ z, Q z*logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration z.1)) := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hQ1,one_mul]
    rw [inverseLog_expectation G order d x p w n D Q]
  rw [he] at hm
  have hi := conditioned_inverse_cost_bs G order d x p w s n D horder ho hd hp h0 h1 hc hc1 hconn hδ hD
  have hl := (conditioned_configuration_entropy_bs G order d x p w ho hd hp h0 h1 hc hc1 hconn s n D hδ hD).2
  change divergence (outputMass G order d x p w s n D) μ ≤ _ at hm
  change _ ≤ (4*(16/(2*p*(1-p)))+6)*L+(2*(16/(2*p*(1-p)))+5)*n*Real.log 4
  calc
    _ ≤ _ := hm
    _ ≤ L + (2*(((16/(2*p*(1-p)))*(2*L+n*Real.log 4))+2*L+2*n*Real.log 4) + (L+n*Real.log 4)) :=
      add_le_add (le_refl L) (add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2)) hl)
    _ = _ := by ring

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_FiniteEventEntropy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma supported_event_entropy (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (hR : ∀ x, 0 < R x) (A : Set X)
    (hs : ∀ x, P x ≠ 0 → x ∈ A) :
    0 < (∑ x, if x ∈ A then R x else 0) ∧
      Real.log (1/(∑ x, if x ∈ A then R x else 0)) ≤ divergence P R := by
  let R' : X → ℝ := fun x => if x ∈ A then R x else 0
  have hn : ∀ x, 0 ≤ R' x := by
    intro x
    unfold R'
    split_ifs
    · exact (hR x).le
    · exact le_rfl
  have hp : ∀ x, 0 < P x → 0 < R' x := by
    intro x hx
    simp only [R',ite_eq_left (hs x hx.ne')]
    exact hR x
  have ho : 0 < ∑ x, R' x := by
    have hh := normalizer_pos P R' hP hn hP1 hp (fun _ => 0)
    simpa only [Real.exp_zero,mul_one] using hh
  refine ⟨ho,?_⟩
  have hh := log_sum_inequality P R' hP hn hp
  rw [hP1,one_mul] at hh
  refine hh.trans_eq ?_
  unfold divergence
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x=0
  · simp only [hx,zero_mul]
  · simp only [R',ite_eq_left (hs x hx)]

omit [Fintype Y] in
lemma pushMass_supported (P : X → ℝ) (f : X → Y) (A : Set Y)
    (hs : ∀ x, P x ≠ 0 → f x ∈ A) (y : Y) (hy : pushMass f P y ≠ 0) : y ∈ A := by
  by_contra hn
  apply hy
  unfold pushMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : f x=y
  · rw [ite_eq_left hx]
    by_contra hp
    exact hn (hx ▸ hs x hp)
  · exact ite_eq_right hx

end CriticalPercolation.FiniteEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryEventBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.eventBoundFinDec
lemma prob_bits (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (P : Set E → Prop) :
    (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) =
      prob w P := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  have he := expect_configuration w (fun η => if P η then (1:ℝ) else 0)
  rw [← hw] at he
  simpa only [expect,prob,mul_ite,mul_one,mul_zero] using he

theorem conditioned_event_bound_bs_oai (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let t := interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))
    0 < prob w (endpointEvent G (x t.1) (x t.2) s) ∧
      -Real.log (prob w (endpointEvent G (x t.1) (x t.2) s)) ≤
      (4*(16/(2*p*(1-p)))+6)*constructionCost G order d x p w c s n D +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 := by
  dsimp only
  let t := interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))
  let P := endpointEvent G (x t.1) (x t.2) s
  let Q := conditionedMass G order d x p w s n D
  let f : ((E → Bool) × (Fin n → Option E)) → (E → Bool) := fun z => stage n D z.1 z.2 n
  have hQ := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z=1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hh := supported_event_entropy (pushMass f Q) (FiniteProduct.density (QueryTree.bitWeight p))
    (pushMass_nonneg f Q hQ) ((pushMass_sum f Q).trans hQ1)
    (fun ω => Finset.prod_pos fun e _ => QueryTree.bitWeight_pos hp e (ω e))
    {ω | P (configuration ω)}
    (pushMass_supported Q f {ω | P (configuration ω)} (fun z hz =>
      stage_endpointEvent G order d x p w s n D z.1 z.2 hz))
  have hb := prob_bits p w h0 h1 P
  change (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) = _ at hb
  change 0 < (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) ∧ _ at hh
  rw [hb] at hh
  have hl := conditioned_output_entropy G order d x p w s n D horder ho hd hp h0 h1 hc hc1 hconn hδ hD
  refine ⟨hh.1,?_⟩
  have he := hh.2.trans hl
  simp only [Set.mem_ofPred_eq] at he
  rw [hb] at he
  simpa only [one_div,Real.log_inv] using he

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs_oai.{u_1, u_2}
