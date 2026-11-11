-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:03.857203+00:00
-- url     : https://prove2.me/submissions/5ded4871-11fb-4847-9ea4-69be9c3df3ea

import Mathlib
import Definitions.Def_OAIQ240Bp011

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_FiniteExtensions
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem compactPerturbation_filtration_stops (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (V : ℕ → Submodule ℝ E) (hmono : Monotone V)
    (hclosed : ∀ n, IsClosed (V n : Set E))
    (hstep : ∀ n x, x∈V (n+1) → x+T x∈V n) :
    ∃ n, V n=V (n+1) := by
  by_contra! hne
  have hx (n : ℕ) : ∃ x∈V (n+1), ‖x‖≤3 ∧ ∀ y∈V n, 1≤‖x-y‖ := by
    have hn : ¬ V (n+1) ≤ V n := fun h => hne n (le_antisymm (hmono (Nat.le_succ n)) h)
    obtain ⟨x,hxs,hxn⟩ := Set.not_subset.mp hn
    have hc : IsClosed ((V n).comap (V (n+1)).subtype : Set (V (n+1))) :=
      (hclosed n).preimage continuous_subtype_val
    have hh : ∃ x : V (n+1), x∉(V n).comap (V (n+1)).subtype := ⟨⟨x,hxs⟩,hxn⟩
    obtain ⟨⟨x,hx⟩,hxn,hxy⟩ := riesz_lemma_of_norm_lt
      (c := (2:ℝ)) (by norm_num) (R := 3) (by norm_num) hc hh
    refine ⟨x,hx,hxn,fun y hy => ?_⟩
    exact hxy ⟨y,hmono (Nat.le_succ n) hy⟩ hy
  choose x hxv hxn hxy using hx
  have hTx {n m : ℕ} (hnm : n+1 ≤ m) : T (x n)∈V m := by
    have hs : x n+T (x n) ∈ V m := hmono (by omega) (hstep n (x n) (hxv n))
    have hz : x n∈V m := hmono hnm (hxv n)
    simpa only [add_sub_cancel_left] using (V m).sub_mem hs hz
  have hp : Pairwise (fun m n : ℕ => 1≤‖T (x m)-T (x n)‖) := by
    have : Std.Symm (fun m n : ℕ => 1≤‖T (x m)-T (x n)‖) :=
      ⟨fun _ _ h => by rwa [norm_sub_rev]⟩
    apply Pairwise.of_lt
    intro m n hmn
    let y := x n+T (x n)-T (x m)
    have hy : y∈V n := (V n).sub_mem (hstep n (x n) (hxv n)) (hTx (by omega))
    have he : x n-y=T (x m)-T (x n) := by dsimp [y]; abel
    simpa only [he] using hxy n y hy
  obtain ⟨K,hK,hTK⟩ := hT.image_closedBall_subset_compact 3
  obtain ⟨y,_,φ,hφ,hφy⟩ := hK.tendsto_subseq (fun n => hTK ⟨x n,by simpa using hxn n,rfl⟩)
  have hh := hφy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hh
  obtain ⟨N,hN⟩ := hh 1 (by norm_num)
  have hlt : ‖T (x (φ (N+1)))-T (x (φ N))‖<1 := by
    simpa only [Function.comp_apply,dist_eq_norm_sub,ContinuousLinearMap.coe_coe] using hN (N+1) (by omega)
  exact hlt.not_ge (hp (hφ.injective.ne (by omega)))

 theorem compactPerturbation_kernel_stabilizes (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    ∃ n, ((ContinuousLinearMap.id ℝ E+T : E →L[ℝ] E).toLinearMap^n).ker=
      ((ContinuousLinearMap.id ℝ E+T : E →L[ℝ] E).toLinearMap^(n+1)).ker := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+T
  apply compactPerturbation_filtration_stops T hT (fun n => (P.toLinearMap^n).ker)
    P.toLinearMap.iterateKer.monotone
  · intro n
    rw [←ContinuousLinearMap.toLinearMap_pow]
    exact (P^n).isClosed_ker
  · intro n x hx
    change (P.toLinearMap^n) (P.toLinearMap x)=0
    change (P.toLinearMap^(n+1)) x=0 at hx
    simpa only [pow_succ,Module.End.mul_apply] using hx

 theorem compactPerturbation_injective_of_surjective (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hs : Surjective (ContinuousLinearMap.id ℝ E+T)) :
    Injective (ContinuousLinearMap.id ℝ E+T) := by
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E+T
  obtain ⟨n,hn⟩ := compactPerturbation_kernel_stabilizes T hT
  change (P.toLinearMap^n).ker=(P.toLinearMap^(n+1)).ker at hn
  apply (LinearMap.ker_eq_bot (f := P.toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hp : ∀ n : ℕ, Surjective (P.toLinearMap^n) := by
    intro m
    induction m with
    | zero => exact fun y => ⟨y,rfl⟩
    | succ m hm =>
      intro y
      obtain ⟨z,hz⟩ := hm y
      obtain ⟨x,hx⟩ := hs z
      refine ⟨x,?_⟩
      rw [pow_succ,Module.End.mul_apply]
      exact (congrArg (P.toLinearMap^m) hx).trans hz
  obtain ⟨y,rfl⟩ := hp n x
  have hy : y∈(P.toLinearMap^(n+1)).ker := by
    change (P.toLinearMap^(n+1)) y=0
    simpa only [pow_succ',Module.End.mul_apply] using hx
  rw [←hn] at hy
  exact hy


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_CompactFredholmAlternative
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_surjective_of_injective (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hi : Injective (ContinuousLinearMap.id ℝ E+T)) :
    Surjective (ContinuousLinearMap.id ℝ E+T) := by
  obtain he | hr := hT.hasEigenvalue_or_mem_resolventSet (μ := (-1:ℝ)) (by norm_num)
  · exfalso
    apply he
    rw [Module.End.genEigenspace_one]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hi
    change x+T x=0+T 0
    have hx' : T x-(-1:ℝ) • x=0 := hx
    simpa only [neg_smul,one_smul,sub_neg_eq_add,add_comm,map_zero,add_zero] using hx'
  · rw [spectrum.mem_resolventSet_iff,←IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at hr
    convert hr.2 using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [add_comm]

 theorem compactPerturbation_injective_iff_surjective (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    Injective (ContinuousLinearMap.id ℝ E+T) ↔ Surjective (ContinuousLinearMap.id ℝ E+T) :=
  ⟨compactPerturbation_surjective_of_injective T hT,
    compactPerturbation_injective_of_surjective T hT⟩

end HigherDimensionalBallPacking.Rigidity

namespace ContinuousLinearMap.FredholmPackage
open scoped _root_.ContinuousLinearMap _root_.ContinuousLinearMap.FredholmPackage
open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {P : E →L[ℝ] F}

 theorem finitePerturbation_compact (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) : IsCompactOperator (finitePerturbation pkg L) := by
  let := pkg.decDom.finite_X₀
  have hc : IsCompactOperator (ContinuousLinearMap.id ℝ pkg.decDom.X₀) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mpr inferInstance
  exact (hc.clm_comp (pkg.decCodom.X₀.subtypeL.comp L)).comp_clm
    (pkg.decDom.X₀.projectionOntoL _ pkg.decDom.isTopCompl.symm)

 theorem finitePerturbation_injective (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) :
    Injective (P+finitePerturbation pkg L) ↔ Injective L := by
  constructor
  · intro hi x y hxy
    have hh : (P+finitePerturbation pkg L) ((domCoords pkg).symm (0,x)) =
        (P+finitePerturbation pkg L) ((domCoords pkg).symm (0,y)) := by
      apply (codCoords pkg).injective
      rw [finitePerturbation_coords pkg,finitePerturbation_coords pkg,
        ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply,hxy]
    have h := congrArg (domCoords pkg) (hi hh)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,Prod.mk.injEq,true_and] using h
  · intro hi x y hxy
    apply (domCoords pkg).injective
    have hh := congrArg (codCoords pkg) hxy
    rw [finitePerturbation_coords pkg,finitePerturbation_coords pkg] at hh
    exact Prod.ext (pkg.equiv.injective (congrArg Prod.fst hh)) (hi (congrArg Prod.snd hh))

 theorem finitePerturbation_surjective (pkg : _root_.ContinuousLinearMap.FredholmPackage P)
    (L : pkg.decDom.X₀ →L[ℝ] pkg.decCodom.X₀) :
    Surjective (P+finitePerturbation pkg L) ↔ Surjective L := by
  constructor
  · intro hs y
    obtain ⟨x,hx⟩ := hs ((codCoords pkg).symm (0,y))
    refine ⟨((domCoords pkg) x).2,?_⟩
    have hh := congrArg (codCoords pkg) hx
    rw [finitePerturbation_coords pkg,ContinuousLinearEquiv.apply_symm_apply] at hh
    exact congrArg Prod.snd hh
  · intro hs y
    obtain ⟨x,hx⟩ := hs ((codCoords pkg) y).2
    refine ⟨(domCoords pkg).symm (pkg.equiv.symm ((codCoords pkg) y).1,x),?_⟩
    apply (codCoords pkg).injective
    rw [finitePerturbation_coords pkg,ContinuousLinearEquiv.apply_symm_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply,hx,Prod.mk.eta]

end ContinuousLinearMap.FredholmPackage

namespace HigherDimensionalBallPacking.Rigidity
open Function
open Set
open _root_.OAI.ContinuousLinearMap.FredholmPackage
section

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

 theorem finrank_eq_of_map_alternative
    (h : ∀ L : E →L[ℝ] F, Injective L ↔ Surjective L) :
    Module.finrank ℝ E=Module.finrank ℝ F := by
  apply le_antisymm
  · by_contra! hlt
    have hr : Module.rank ℝ F < Module.rank ℝ E := by
      rw [←Module.finrank_eq_rank,←Module.finrank_eq_rank]
      exact_mod_cast hlt
    obtain ⟨g,hg⟩ := Module.Free.exists_linearMap_injective_of_rank_lt hr
    obtain ⟨L,hL⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
    have hLs : Surjective L := by
      intro y
      refine ⟨g y,?_⟩
      exact congrArg (fun A : F →ₗ[ℝ] F => A y) hL
    have hLi : Injective L := (h L.toContinuousLinearMap).mpr hLs
    exact hlt.not_ge (LinearMap.finrank_le_finrank_of_injective hLi)
  · by_contra! hlt
    have hr : Module.rank ℝ E < Module.rank ℝ F := by
      rw [←Module.finrank_eq_rank,←Module.finrank_eq_rank]
      exact_mod_cast hlt
    obtain ⟨L,hLi⟩ := Module.Free.exists_linearMap_injective_of_rank_lt hr
    have hLs : Surjective L := (h L.toContinuousLinearMap).mp hLi
    exact hlt.not_ge (LinearMap.finrank_le_finrank_of_surjective hLs)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_package_finrank_bp240_oai (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (pkg : (ContinuousLinearMap.id ℝ E+T).FredholmPackage) :
    Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀ := by
  let := pkg.decDom.finite_X₀
  let := pkg.decCodom.finite_X₀
  apply finrank_eq_of_map_alternative
  intro L
  have hc : IsCompactOperator (T+finitePerturbation pkg L) :=
    hT.add (finitePerturbation_compact pkg L)
  have hh := compactPerturbation_injective_iff_surjective (T+finitePerturbation pkg L) hc
  rw [←add_assoc] at hh
  exact (finitePerturbation_injective pkg L).symm.trans (hh.trans (finitePerturbation_surjective pkg L))

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank_bp240_oai.{u_1} := @OAI.HigherDimensionalBallPacking.Rigidity.compactPerturbation_package_finrank_bp240_oai.{u_1}
