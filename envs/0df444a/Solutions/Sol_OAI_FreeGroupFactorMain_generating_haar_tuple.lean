-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.generating_haar_tuple
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:16:53.649446+00:00
-- url     : https://prove2.me/submissions/18d35836-cd5b-42c0-88be-b4c5a84c8fbc

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_Generation_orbit_local_approximation

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

theorem word_initial (n : ℕ) (g : FreeGroup (Fin n)) :
    word (initial n) g = groupUnitary (FreeGroup.map Option.some g) := by
  have he : word (initial n) =
      (unitary (Ambient n)).subtype.comp
        ((groupUnitaryUHom (FreeGroup (Option (Fin n)))).comp (FreeGroup.map Option.some)) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.map.of]
    rfl
  exact DFunLike.congr_fun he g

theorem orbit_nonempty (n : ℕ) : (orbit n).Nonempty := by
  refine ⟨mapTuple (StarAlgEquiv.refl ℂ (Ambient n)) (initial n),StarAlgEquiv.refl ℂ (Ambient n),?_,rfl⟩
  intro T
  rfl

theorem poly_groupL2_continuous (n : ℕ) (p : FreeGroup (Fin n) →₀ ℂ) :
    Continuous (fun U : Tuple n => groupL2 (poly U p)) :=
  (groupL2 (G := FreeGroup (Option (Fin n)))).continuous.comp (poly_continuous p)

theorem orbit_trace (n : ℕ) (U : Tuple n) (hU : U ∈ orbit n) (g : FreeGroup (Fin n)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  obtain ⟨Φ,ht,rfl⟩ := hU
  rw [word_mapTuple,ht,word_initial,canonicalTrace_groupUnitary]
  have hi : FreeGroup.map (Option.some : Fin n → Option (Fin n)) g = 1 ↔ g = 1 := by
    rw [← (FreeGroup.map Option.some).map_one]
    exact (FreeGroup.map_injective (Option.some_injective (Fin n))).eq_iff
  simp only [hi]

theorem closure_orbit_trace (n : ℕ) (U : Tuple n) (hU : U ∈ closure (orbit n)) (g : FreeGroup (Fin n)) :
    canonicalTrace (word U g) = if g = 1 then 1 else 0 := by
  classical
  have hc : Continuous (fun V : Tuple n => canonicalTrace (word V g)) :=
    (canonicalTraceCLM (G := FreeGroup (Option (Fin n)))).continuous.comp (word_continuous g)
  have hclosed : IsClosed {V : Tuple n | canonicalTrace (word V g) = if g = 1 then 1 else 0} :=
    isClosed_eq hc continuous_const
  exact (closure_minimal (fun V hV => orbit_trace n V hV g) hclosed) hU

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

theorem generating_haar_tuple (n : ℕ) (hn : 3 ≤ n) :
    ∃ U : Tuple n,
      (∀ g : FreeGroup (Fin n), canonicalTrace (word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (word U g)))).topologicalClosure := by
  classical
  obtain ⟨U,hU,happrox⟩ := baire_local_approximation (orbit n) (orbit_nonempty n)
    (fun p U => groupL2 (poly U p)) (poly_groupL2_continuous n)
    (fun g : FreeGroup (Option (Fin n)) => lp.single 2 g (1 : ℂ))
    (orbit_local_approximation n hn)
  exact ⟨U,closure_orbit_trace n U hU,total_of_poly_approx U happrox⟩

end FreeGroupFactorMain

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.generating_haar_tuple := @OAI.FreeGroupFactorMain.generating_haar_tuple
