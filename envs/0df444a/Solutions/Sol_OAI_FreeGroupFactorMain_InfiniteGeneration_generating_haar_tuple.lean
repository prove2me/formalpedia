-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.InfiniteGeneration.generating_haar_tuple
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:13:44.537902+00:00
-- url     : https://prove2.me/submissions/1b23cff0-d794-483e-a3e4-518dbe7f9893

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

theorem canonicalTrace_eq_inner {G : Type uG} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) :
    canonicalTrace T = inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
      ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))) := by
  classical
  simp only [canonicalTrace, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply congrArg (fun v : GroupHilbert G => ((T : GroupOperator G) v) 1)
  ext b
  simp [lp.single_apply, Pi.single_apply]

def canonicalTraceLinear {G : Type uG} [Group G] : groupVonNeumann G →ₗ[ℂ] ℂ where
  toFun := canonicalTrace
  map_add' T U := by simp [canonicalTrace]
  map_smul' c T := by simp [canonicalTrace]

theorem norm_canonicalTrace_le {G : Type uG} [Group G] (T : groupVonNeumann G) :
    ‖canonicalTrace T‖ ≤ ‖T‖ := by
  classical
  rw [canonicalTrace_eq_inner]
  calc
    ‖inner ℂ (lp.single 2 (1 : G) (1 : ℂ))
        ((T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ)))‖ ≤
        ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖ := norm_inner_le_norm _ _
    _ ≤ ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖ *
        (‖(T : GroupOperator G)‖ * ‖lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ)‖) := by
      gcongr
      exact (T : GroupOperator G).le_opNorm _
    _ = ‖T‖ := by simp

def canonicalTraceCLM {G : Type uG} [Group G] : groupVonNeumann G →L[ℂ] ℂ :=
  canonicalTraceLinear.mkContinuous 1 (fun T => by
    change ‖canonicalTrace T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_canonicalTrace_le T)

@[simp] theorem canonicalTraceCLM_apply {G : Type uG} [Group G] (T : groupVonNeumann G) :
    canonicalTraceCLM T = canonicalTrace T := rfl

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

 def groupUnitaryHom (G : Type uG) [Group G] : G →* groupVonNeumann G where
  toFun := groupUnitary
  map_one' := Subtype.ext (leftRegular_one)
  map_mul' g b := Subtype.ext (leftRegular_mul g b)

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

omit [Group G] in
theorem group_single_total [DecidableEq G] (K : Submodule ℂ (GroupHilbert G))
    (hK : IsClosed (K : Set (GroupHilbert G)))
    (hsingle : ∀ g : G, lp.single 2 g (1 : ℂ) ∈ K) : ⊤ ≤ K := by
  classical
  intro ξ _hξ
  have hs := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro g _hg
  have he : lp.single 2 g (ξ g) = (ξ g) • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    ext x
    simp [lp.single_apply, Pi.single_apply]
  rw [he]
  exact K.smul_mem _ (hsingle g)

variable {ι : Type uι}

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

end

theorem poly_l2_mem {G : Type uG} [Group G] {ι : Type uι}
    (U : ι → unitary (groupVonNeumann G)) (p : FreeGroup ι →₀ ℂ) :
    groupL2 (poly U p) ∈ Submodule.span ℂ (Set.range (fun g => groupL2 (word U g))) := by
  classical
  rw [poly,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro g _hg
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g,rfl⟩)

theorem total_of_poly_approx {G : Type uG} [Group G] [DecidableEq G] {ι : Type uι}
    (U : ι → unitary (groupVonNeumann G))
    (hU : ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ p : FreeGroup ι →₀ ℂ,
      dist (groupL2 (poly U p)) (lp.single 2 g (1 : ℂ)) < ε) :
    ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
  intro g
  change lp.single 2 g (1 : ℂ) ∈ closure (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g))) : Set (GroupHilbert G))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := hU g ε hε
  exact ⟨groupL2 (poly U p),poly_l2_mem U p,by simpa only [dist_comm] using hp⟩

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

theorem baire_local_approximation
    {X : Type uX} {Y : Type uY} {I : Type uI} {P : Type uP} [MetricSpace X] [CompleteSpace X] [MetricSpace Y] [Countable I]
    (S : Set X) (hS : S.Nonempty) (a : P → X → Y) (ha : ∀ p, Continuous (a p))
    (v : I → Y)
    (hlocal : ∀ x ∈ S, ∀ δ : ℝ, 0 < δ → ∀ i : I, ∀ ε : ℝ, 0 < ε →
      ∃ y ∈ S, dist y x < δ ∧ ∃ p, dist (a p y) (v i) < ε) :
    ∃ x ∈ closure S, ∀ i : I, ∀ ε : ℝ, 0 < ε → ∃ p, dist (a p x) (v i) < ε := by
  let T := closure S
  let : IsClosed T := isClosed_closure
  let : Nonempty T := by
    obtain ⟨x,hx⟩ := hS
    exact ⟨⟨x, subset_closure hx⟩⟩
  let O (ik : I × ℕ) : Set T := {x | ∃ p, dist (a p x) (v ik.1) < 1 / (ik.2 + 1 : ℝ)}
  have hopen (ik : I × ℕ) : IsOpen (O ik) := by
    simp only [O, Set.ofPred_exists]
    apply isOpen_iUnion
    intro p
    exact isOpen_lt (((ha p).comp continuous_subtype_val).dist continuous_const) continuous_const
  have hdense (ik : I × ℕ) : Dense (O ik) := by
    intro x
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp x.property (δ/2) (half_pos hδ)
    obtain ⟨z,hz,hzy,p,hp⟩ := hlocal y hy (δ/2) (half_pos hδ) ik.1
      (1/(ik.2+1:ℝ)) (by positivity)
    refine ⟨⟨z,subset_closure hz⟩, ⟨p,hp⟩, ?_⟩
    change dist (x : X) z < δ
    have htri := dist_triangle (x : X) y z
    rw [dist_comm y z] at htri
    linarith
  obtain ⟨x,hx⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  refine ⟨x,x.property,?_⟩
  intro i ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨p,hp⟩ := Set.mem_iInter.mp hx (i,k)
  exact ⟨p, hp.trans hk⟩

open Generation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.Generation

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

theorem word_initial (g : FreeGroup (Fin 3)) :
    word initial g = groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) g) := by
  have he : word initial = (groupUnitaryHom Group).comp
      (FreeGroup.map (fun i => some (Sum.inl i))) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.map.of]
    rfl
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain.InfiniteGeneration

namespace FreeGroupFactorMain.Generation
variable {G : Type uG} [Group G] {ι : Type uι}

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

 theorem orbit_nonempty : orbit.Nonempty := by
  refine ⟨mapTuple (StarAlgEquiv.refl ℂ M) initial,StarAlgEquiv.refl ℂ M,?_,rfl⟩
  intro T
  rfl

 theorem orbit_trace (U : Tuple) (hU : U ∈ orbit) (g : FreeGroup (Fin 3)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  rw [word_mapTuple,ht,word_initial,canonicalTrace_groupUnitary]
  have hinj : Function.Injective (fun i : Fin 3 => (some (Sum.inl i) : Index)) :=
    Option.some_injective _ |>.comp Sum.inl_injective
  have hi : FreeGroup.map (fun i : Fin 3 => (some (Sum.inl i) : Index)) g = 1 ↔ g = 1 := by
    rw [← (FreeGroup.map (fun i : Fin 3 => (some (Sum.inl i) : Index))).map_one]
    exact (FreeGroup.map_injective hinj).eq_iff
  simp only [hi]

 theorem closure_orbit_trace (U : Tuple) (hU : U ∈ closure orbit) (g : FreeGroup (Fin 3)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  have hc : Continuous (fun V : Tuple => canonicalTrace (word V g)) :=
    (canonicalTraceCLM (G := Group)).continuous.comp (word_continuous g)
  have hclosed : IsClosed {V : Tuple | canonicalTrace (word V g) = if g = 1 then 1 else 0} :=
    isClosed_eq hc continuous_const
  exact (closure_minimal (fun V hV => orbit_trace V hV g) hclosed) hU

 theorem generating_haar_tuple
    (hlocal : ∀ U ∈ orbit, ∀ δ : ℝ, 0 < δ → ∀ g : Group, ∀ ε : ℝ, 0 < ε →
      ∃ V ∈ orbit, dist V U < δ ∧ ∃ p : FreeGroup (Fin 3) →₀ ℂ,
        dist (groupL2 (poly V p)) (lp.single 2 g (1 : ℂ)) < ε) :
    ∃ U : Tuple,
      (∀ g : FreeGroup (Fin 3), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  obtain ⟨U,hU,happrox⟩ := baire_local_approximation orbit orbit_nonempty
    (fun p U => groupL2 (poly U p))
    (fun p => (groupL2 (G := Group)).continuous.comp (poly_continuous p))
    (fun g : Group => lp.single 2 g (1 : ℂ)) hlocal
  exact ⟨U,closure_orbit_trace U hU,total_of_poly_approx U happrox⟩

end FreeGroupFactorMain.InfiniteGeneration

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.InfiniteGeneration.generating_haar_tuple := @OAI.FreeGroupFactorMain.InfiniteGeneration.generating_haar_tuple
