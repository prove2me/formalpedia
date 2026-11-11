-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.framed_compact_perturbation_fredholm_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:05.04587+00:00
-- url     : https://prove2.me/submissions/f6d7a735-e138-4036-b708-986a858c783f

import Mathlib
import Definitions.Def_OAIQ240Bp011
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_compactPerturbation_package_finrank_bp240

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

 theorem compactPerturbation_finite_kernel (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E+T).ker := by
  let S := ContinuousLinearMap.id ℝ E+T
  have h : ∀ x : S.ker, T x=-(x:E) := by
    intro x
    have hx := x.property
    change (x:E)+T x=0 at hx
    exact eq_neg_of_add_eq_zero_right hx
  have hc := (hT.comp_clm S.ker.subtypeL).neg
  have hm : ∀ x : S.ker, -(T (x:E))∈S.ker := by
    intro x
    rw [h,neg_neg]
    exact x.property
  have hk := hc.codRestrict hm S.isClosed_ker
  have he : Set.codRestrict (fun x : S.ker => -(T (x:E))) S.ker hm=id := by
    funext x
    apply Subtype.ext
    change -(T (x:E))=(x:E)
    rw [h,neg_neg]
  change IsCompactOperator (Set.codRestrict (fun x : S.ker => -(T (x:E))) S.ker hm) at hk
  rw [he] at hk
  exact FiniteDimensional.of_isCompactOperator_id hk


end
section
open Set Function Filter Topology
open scoped NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem compactPerturbation_antilipschitz
    (P T : E →L[ℝ] F) {K : ℝ≥0} (hP : AntilipschitzWith K P)
    (hT : IsCompactOperator T) (hi : Injective (P+T)) :
    ∃ C, AntilipschitzWith C (P+T) := by
  rw [antilipschitzWith_iff_exists_mul_le_norm]
  by_contra! h
  obtain ⟨φ, _, hφpos, hφ⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  have hx : ∀ n : ℕ, ∃ x : E, ‖x‖=1 ∧ ‖(P+T) x‖<φ n := by
    intro n
    obtain ⟨x,hx⟩ := h (φ n) (hφpos n)
    have hn : 0<‖x‖ := by
      by_contra! hh
      have hx0 : x=0 := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
      subst x
      simp at hx
    refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
    · rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
      calc
        ‖x‖⁻¹ * ‖(P+T) x‖ < ‖x‖⁻¹ * (φ n * ‖x‖) := mul_lt_mul_of_pos_left hx (inv_pos.mpr hn)
        _=φ n := by field_simp
  choose x hxn hxb using hx
  have hxlim : Tendsto (fun n => (P+T) (x n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hxb n).le) hφ
  obtain ⟨A,hA,hAT⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y,_,ψ,hψ,hy⟩ := hA.tendsto_subseq
    (fun n => hAT ⟨x n, by simp only [Metric.mem_closedBall,dist_zero_right,hxn,le_refl],rfl⟩)
  have hp : Tendsto (fun n => P (x (ψ n))) atTop (𝓝 (-y)) := by
    have hh := (hxlim.comp hψ.tendsto_atTop).sub hy
    simpa only [comp_apply,add_apply,ContinuousLinearMap.coe_coe,add_sub_cancel_right,zero_sub] using hh
  have hc : CauchySeq (x ∘ ψ) := by
    have hh := hp.cauchySeq
    change Cauchy (Filter.map P (Filter.map (x ∘ ψ) atTop)) at hh
    exact (hP.isUniformInducing P.uniformContinuous).cauchy_map_iff.mp hh
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hc
  have hs : (P+T) z=0 :=
    tendsto_nhds_unique ((P+T).continuous.continuousAt.tendsto.comp hz)
      (hxlim.comp hψ.tendsto_atTop)
  have hz0 : z=0 := hi (hs.trans (map_zero (P+T)).symm)
  have hn : ‖z‖=1 := tendsto_nhds_unique (hz.norm)
    (by simpa only [comp_apply,hxn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  simp only [hz0,norm_zero,zero_ne_one] at hn


end
section
open scoped NNReal
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_closed_range (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    IsClosed ((ContinuousLinearMap.id ℝ E+T).range : Set E) := by
  let S := ContinuousLinearMap.id ℝ E+T
  have : FiniteDimensional ℝ S.ker := compactPerturbation_finite_kernel T hT
  obtain ⟨N,hNc,hN⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional S.ker).exists_isClosed_isCompl
  let : IsClosed (N : Set E) := hNc
  have hp : AntilipschitzWith 1 N.subtypeL :=
    (isometry_subtype_coe : Isometry (Subtype.val : N → E)).antilipschitz
  have hi : Injective (N.subtypeL+T.comp N.subtypeL) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hh : (x:E)-(y:E)∈S.ker := by
      change S ((x:E)-(y:E))=0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hh' : (x:E)-(y:E)∈(⊥ : Submodule ℝ E) :=
      hN.disjoint.le_bot ⟨hh,N.sub_mem x.property y.property⟩
    exact hh'
  obtain ⟨C,hC⟩ := compactPerturbation_antilipschitz N.subtypeL (T.comp N.subtypeL)
    hp (hT.comp_clm N.subtypeL) hi
  have hc := hC.isClosed_range (N.subtypeL+T.comp N.subtypeL).uniformContinuous
  have he : Set.range (N.subtypeL+T.comp N.subtypeL)=(S.range : Set E) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨(x:E),rfl⟩
    · rintro ⟨x,rfl⟩
      have hx : x∈S.ker⊔N := by rw [hN.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨b,hb⟩,?_⟩
      change S b=S x
      rw [←hab,map_add,show S a=0 from ha,zero_add]
  rwa [he] at hc

 theorem compactPerturbation_strict (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    IsStrictMap (ContinuousLinearMap.id ℝ E+T) := by
  let S := ContinuousLinearMap.id ℝ E+T
  let : IsClosed (S.range : Set E) := compactPerturbation_closed_range T hT
  let F : E →L[ℝ] S.range := S.codRestrict S.range (fun x => ⟨x,rfl⟩)
  have hf : Surjective F := by
    rintro ⟨y,x,hx⟩
    exact ⟨x,Subtype.ext hx⟩
  exact F.isQuotientMap hf


end
section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem compactPerturbation_finite_cokernel (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hc : IsClosed ((ContinuousLinearMap.id ℝ E+T).range : Set E)) :
    FiniteDimensional ℝ (E ⧸ (ContinuousLinearMap.id ℝ E+T).range) := by
  let S := ContinuousLinearMap.id ℝ E+T
  let Q := S.range.mkQL
  have he : ∀ x, -(Q (T x))=Q x := by
    intro x
    have hh : Q (S x)=0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩
    change Q (x+T x)=0 at hh
    rw [map_add] at hh
    exact (eq_neg_of_add_eq_zero_left hh).symm
  have hQ : IsCompactOperator Q := by
    have hh := (hT.clm_comp Q).neg
    have he' : -(Q ∘ T)=Q := by funext x; exact he x
    rwa [he'] at hh
  obtain ⟨K,hK,hKQ⟩ := hQ
  have hK0 : K∈𝓝 (0 : E ⧸ S.range) := by
    have hm := S.range.isOpenMap_mkQ.map_nhds_eq (x := 0)
      S.range.continuous_mkQ.continuousAt
    rw [map_zero] at hm
    rw [←hm]
    exact hKQ
  let : IsClosed (S.range : Set E) := hc
  exact FiniteDimensional.of_isCompactOperator_id ⟨K,hK,hK0⟩


end
section
open Set Function Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_fredholm (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    (ContinuousLinearMap.id ℝ E+T).IsFredholm := by
  have : FiniteDimensional ℝ (ContinuousLinearMap.id ℝ E+T).ker :=
    compactPerturbation_finite_kernel T hT
  exact {
    isStrictMap := compactPerturbation_strict T hT
    isClosed_range := compactPerturbation_closed_range T hT
    finite_ker := this
    finite_coker := compactPerturbation_finite_cokernel T hT (compactPerturbation_closed_range T hT)
    closedComplemented_ker := Submodule.ClosedComplemented.of_finiteDimensional _ }


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
open Function
open Set
open _root_.OAI.ContinuousLinearMap.FredholmPackage

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem compactPerturbation_index_zero (T : E →L[ℝ] E) (hT : IsCompactOperator T) :
    Module.finrank ℝ (ContinuousLinearMap.id ℝ E+T).ker=
      Module.finrank ℝ (E ⧸ (ContinuousLinearMap.id ℝ E+T).range) := by
  obtain ⟨pkg⟩ := (compactPerturbation_fredholm T hT).nonempty_fredholmPackage
  have hd := compactPerturbation_package_finrank_bp240 T hT pkg
  rw [pkg.ker_eq,pkg.range_eq]
  exact hd.trans (Submodule.quotientEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl).finrank_eq.symm

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
open Set Function

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma fredholm_post_equiv (L : E →L[ℝ] F) (hL : L.IsFredholm) (e : F ≃L[ℝ] G) :
    (e.toContinuousLinearMap.comp L).IsFredholm := by
  obtain ⟨v,hv⟩ := hL.exists_isQuasiInverse
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
    (v := v.comp e.symm.toContinuousLinearMap)
  exact hv.comp e.toLinearEquiv.isQuasiInverse

lemma post_equiv_ker (L : E →L[ℝ] F) (e : F ≃L[ℝ] G) :
    (e.toContinuousLinearMap.comp L).ker = L.ker := by
  ext x
  change e (L x) = 0 ↔ L x = 0
  exact e.map_eq_zero_iff

lemma post_equiv_range (L : E →L[ℝ] F) (e : F ≃L[ℝ] G) :
    L.range.map e.toLinearMap = (e.toContinuousLinearMap.comp L).range := by
  exact (LinearMap.range_comp L.toLinearMap e.toLinearMap).symm

lemma post_equiv_finrank_coker (L : E →L[ℝ] F) (e : F ≃L[ℝ] G) :
    Module.finrank ℝ (F ⧸ L.range) =
      Module.finrank ℝ (G ⧸ (e.toContinuousLinearMap.comp L).range) :=
  (Submodule.Quotient.equiv _ _ e.toLinearEquiv (post_equiv_range L e)).finrank_eq

lemma index_zero_post_equiv (L : E →L[ℝ] F)
    (hL : Module.finrank ℝ L.ker = Module.finrank ℝ (F ⧸ L.range)) (e : F ≃L[ℝ] G) :
    Module.finrank ℝ (e.toContinuousLinearMap.comp L).ker =
      Module.finrank ℝ (G ⧸ (e.toContinuousLinearMap.comp L).range) := by
  rw [post_equiv_ker]
  exact hL.trans (post_equiv_finrank_coker L e)

lemma equiv_add_compact_fredholm [CompleteSpace E] (e : E ≃L[ℝ] F)
    (C : E →L[ℝ] F) (hC : IsCompactOperator C) :
    (e.toContinuousLinearMap+C).IsFredholm := by
  have hT := hC.clm_comp e.symm.toContinuousLinearMap
  have he : e.toContinuousLinearMap+C = e.toContinuousLinearMap.comp
      (ContinuousLinearMap.id ℝ E+e.symm.toContinuousLinearMap.comp C) := by
    ext x; simp
  rw [he]
  exact fredholm_post_equiv _ (compactPerturbation_fredholm _ hT) e

lemma equiv_add_compact_index_zero [CompleteSpace E] (e : E ≃L[ℝ] F)
    (C : E →L[ℝ] F) (hC : IsCompactOperator C) :
    Module.finrank ℝ (e.toContinuousLinearMap+C).ker =
      Module.finrank ℝ (F ⧸ (e.toContinuousLinearMap+C).range) := by
  have hT := hC.clm_comp e.symm.toContinuousLinearMap
  have he : e.toContinuousLinearMap+C = e.toContinuousLinearMap.comp
      (ContinuousLinearMap.id ℝ E+e.symm.toContinuousLinearMap.comp C) := by
    ext x; simp
  rw [he]
  exact index_zero_post_equiv _ (compactPerturbation_index_zero _ hT) e

lemma conjugated_normal_form (P Z : E →L[ℝ] F) (D : E ≃L[ℝ] F) (R : F ≃L[ℝ] F)
    (h : R.toContinuousLinearMap.comp P = D.toContinuousLinearMap-Z) :
    P = (D.trans R.symm).toContinuousLinearMap - R.symm.toContinuousLinearMap.comp Z := by
  apply ContinuousLinearMap.ext
  intro x
  apply R.injective
  have hx := congrArg (fun L : E →L[ℝ] F => L x) h
  simpa only [ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply,map_sub,ContinuousLinearEquiv.apply_symm_apply] using hx

lemma framed_compact_perturbation_fredholm_bp240_oai [CompleteSpace E]
    (P Z C : E →L[ℝ] F) (D : E ≃L[ℝ] F) (R : F ≃L[ℝ] F)
    (h : R.toContinuousLinearMap.comp P = D.toContinuousLinearMap-Z)
    (hZ : IsCompactOperator Z) (hC : IsCompactOperator C) :
    (P+C).IsFredholm ∧ Module.finrank ℝ (P+C).ker = Module.finrank ℝ (F ⧸ (P+C).range) := by
  have he : P+C = (D.trans R.symm).toContinuousLinearMap +
      (C-R.symm.toContinuousLinearMap.comp Z) := by
    rw [conjugated_normal_form P Z D R h]
    abel
  have hc := hC.sub (hZ.clm_comp R.symm.toContinuousLinearMap)
  rw [he]
  exact ⟨equiv_add_compact_fredholm _ _ hc,equiv_add_compact_index_zero _ _ hc⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.framed_compact_perturbation_fredholm_bp240_oai.{u_1, u_2} := @OAI.HigherDimensionalBallPacking.Rigidity.framed_compact_perturbation_fredholm_bp240_oai.{u_1, u_2}
