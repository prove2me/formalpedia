-- Prove2me | solution 1 for OAI.Release061.NashBoundaryChart.scaling_chart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:57:45.274991+00:00
-- url     : https://prove2.me/submissions/9bbcfff2-338e-4362-85d9-5111c51424b8

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateDerivativeRank
attribute [-instance] _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
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

theorem complex_span_real_linear_range {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Submodule.span ℂ (range L) =
      Submodule.span ℂ (range (fun i => L (Pi.single i 1))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hx : x = ∑ i : Fin d, x i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hx,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    change ((x i : ℂ) • L (Pi.single i 1)) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact mem_range_self _

theorem matrix_rank_eq_complex_tangent_dimension {d N : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ)) :
    Matrix.rank (fun j i => L (Pi.single i 1) j) =
      Module.finrank ℂ (Submodule.span ℂ (range L)) := by
  rw [complex_span_real_linear_range L]
  exact Matrix.rank_eq_finrank_span_cols _

theorem complex_tangent_eq_of_rank_ge {d N m : ℕ}
    (L : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℂ))
    (T : Submodule ℂ (Fin N → ℂ)) (hT : Module.finrank ℂ T = m)
    (hLT : ∀ x, L x ∈ T)
    (hr : m ≤ Matrix.rank (fun j i => L (Pi.single i 1) j)) :
    Submodule.span ℂ (range L) = T := by
  have hle : Submodule.span ℂ (range L) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    exact hLT x
  apply Submodule.eq_of_le_of_finrank_eq hle
  apply Nat.le_antisymm (Submodule.finrank_mono hle)
  simpa only [matrix_rank_eq_complex_tangent_dimension,hT] using hr

theorem chart_tangent_finrank {m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ)) {a : Fin m → ℂ}
    (hF : AnalyticAt ℂ F a) (hG : AnalyticAt ℂ G (F a))
    (hGF : (G ∘ F) =ᶠ[𝓝 a] id) :
    Module.finrank ℂ (LinearMap.range (fderiv ℂ F a).toLinearMap) = m := by
  have hcomp := hG.differentiableAt.hasFDerivAt.comp a hF.differentiableAt.hasFDerivAt
  have hid := hcomp.congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (F a)).comp (fderiv ℂ F a) = ContinuousLinearMap.id ℂ _ :=
    hid.unique (hasFDerivAt_id a)
  have hinj : Function.Injective (fderiv ℂ F a) := by
    intro x y hxy
    have hh := congrArg (fderiv ℂ G (F a)) hxy
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh
  simpa using LinearMap.finrank_range_of_inj (f := (fderiv ℂ F a).toLinearMap) hinj

theorem real_derivative_mem_chart_tangent {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF : AnalyticAt ℂ F (G (q x))) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) (v : Fin d → ℝ) :
    fderiv ℝ q x v ∈ LinearMap.range (fderiv ℂ F (G (q x))).toLinearMap := by
  have hGc := hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFc := hF.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hc := hFc.comp x (hGc.comp x hq.hasFDerivAt)
  have he := hc.congr_of_eventuallyEq hFG.symm
  have hd := he.fderiv
  refine ⟨fderiv ℂ G (q x) (fderiv ℝ q x v),?_⟩
  exact (congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) hd).symm

theorem coordinate_derivative_rank {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hq : DifferentiableAt ℝ q x) :
    Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)) =
      Module.finrank ℂ (Submodule.span ℂ (range (fderiv ℝ q x))) := by
  have he (j : Fin N) : fderiv ℝ (fun y => q y j) x =
      (ContinuousLinearMap.proj j).comp (fderiv ℝ q x) := by
    exact ((ContinuousLinearMap.proj j).hasFDerivAt.comp x hq.hasFDerivAt).fderiv
  simp_rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  exact matrix_rank_eq_complex_tangent_dimension (fderiv ℝ q x).toLinearMap

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealPolynomialAnalyticRoot
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

theorem real_analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℝ f a)
    (i : E ≃L[ℝ] F) (hi : HasFDerivAt f (i : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℝ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℝ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm
      (i : E →L[ℝ] F) := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicSupportIndependent
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
open Set
open scoped Classical

theorem complex_independent_of_generic_real_conormals
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [Fintype ι]
    (S : Set E) (hS : Submodule.span ℂ S = ⊤)
    (l : ι → E →ₗ[ℂ] ℂ)
    (hz : ∀ i, ∀ x ∈ S, (l i x).re = 0)
    (hi : LinearIndependent ℝ
      (fun i => Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ))) :
    LinearIndependent ℂ l := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let B : E →ₗ[ℂ] ℂ := ∑ i, (c i).im • l i
  have hBS : S ⊆ LinearMap.ker B := by
    intro x hx
    have hr : (B x).re = 0 := by
      simp [B,LinearMap.sum_apply,LinearMap.smul_apply,hz _ x hx]
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    have him : (B x).im = 0 := by
      simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Complex.re_sum,
        Complex.mul_re,hz _ x hx,mul_zero,zero_sub,Finset.sum_neg_distrib,
        LinearMap.zero_apply,Complex.zero_re,neg_eq_zero] at hh
      simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,Complex.smul_im] using hh
    exact Complex.ext hr him
  have hB : B = 0 := by
    apply LinearMap.ker_eq_top.mp
    apply top_unique
    rw [← hS]
    exact Submodule.span_le.mpr hBS
  have hbi : ∑ i, (c i).im •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hB
    simpa [B,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.smul_re] using hh
  have hci := Fintype.linearIndependent_iff.mp hi (fun i => (c i).im) hbi
  have hbr : ∑ i, (c i).re •
      (Complex.reCLM.toLinearMap.comp ((l i).restrictScalars ℝ)) = 0 := by
    ext x
    have hh := congrArg (fun f : E →ₗ[ℂ] ℂ => (f x).re) hc
    simpa [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
      Complex.mul_re,hci] using hh
  have hcr := Fintype.linearIndependent_iff.mp hi (fun i => (c i).re) hbr
  intro i
  exact Complex.ext (hcr i) (hci i)
end

open Set Filter Topology
open scoped Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericTangentComplexNormal
attribute [-simp] _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
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
open Set
open scoped Classical

theorem independent_functionals_surjective {𝕜 E ι : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι]
    (l : ι → Module.Dual 𝕜 E) (hi : LinearIndependent 𝕜 l) :
    Function.Surjective (LinearMap.pi l) := by
  classical
  have hexp (L : Module.Dual 𝕜 (ι → 𝕜)) (v : ι → 𝕜) :
      L v = ∑ i, v i * L (Pi.single i 1) := by
    have hv : v = ∑ i : ι, v i • Pi.single i (1 : 𝕜) := by
      ext i
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul,smul_eq_mul]
  apply LinearMap.dualMap_injective_iff.mp
  intro L Q hLQ
  have hzero : ∑ i, (L-Q) (Pi.single i 1) • l i = 0 := by
    ext x
    have he := congrArg (fun D : Module.Dual 𝕜 E => D x) hLQ
    change L (fun i => l i x) = Q (fun i => l i x) at he
    have hz : (L-Q) (fun i => l i x) = 0 := sub_eq_zero.mpr he
    rw [hexp] at hz
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      mul_comm,LinearMap.zero_apply] using hz
  have hc := Fintype.linearIndependent_iff.mp hi _ hzero
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  change (L-Q) v = 0
  rw [hexp]
  simp only [hc,mul_zero,Finset.sum_const_zero]

theorem exists_scalar_continuousLinearEquiv_prod_ker
    {𝕜 E X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    (A : E →L[𝕜] X) (hA : Function.Surjective A) :
    ∃ e : E ≃L[𝕜] X × LinearMap.ker A.toLinearMap, ∀ v, (e v).1 = A v := by
  obtain ⟨R,hR⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hA
  let K := LinearMap.ker A.toLinearMap
  let L : E →ₗ[𝕜] X × K :=
    { toFun := fun v => (A v,⟨v-R (A v),by change A (v-R (A v)) = 0; rw [map_sub,hR,sub_self]⟩)
      map_add' := by intro v w; ext <;> simp [map_add]; abel
      map_smul' := by intro c v; ext <;> simp [map_smul,smul_sub] }
  have hinj : Function.Injective L := by
    intro v w he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun p : X × K => (p.2 : E)) he
    change A v = A w at h1
    change v-R (A v) = w-R (A w) at h2
    rw [h1] at h2
    exact sub_left_injective h2
  have hsurj : Function.Surjective L := by
    rintro ⟨x,k⟩
    refine ⟨R x+k,?_⟩
    have hk : A k = 0 := k.property
    have ha : A (R x+k) = x := by rw [map_add,hR,hk,add_zero]
    apply Prod.ext
    · exact ha
    · apply Subtype.ext
      change R x+(k : E)-R (A (R x+k)) = k
      rw [ha]
      abel
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj,hsurj⟩).toContinuousLinearEquiv,fun _ => rfl⟩

lemma submodule_basis_independent {𝕜 E ι : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (S : Submodule 𝕜 E)
    (b : Module.Basis ι 𝕜 S) : LinearIndependent 𝕜 (fun i => (b i : E)) := by
  exact b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)

lemma real_conormal_basis_complex_independent {n k : ℕ}
    (S : Submodule ℝ (Affine n)) (hS : Submodule.span ℂ (S : Set (Affine n)) = ⊤)
    (b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator) :
    LinearIndependent ℂ (fun i => (b i).val.extendRCLike (𝕜 := ℂ)) := by
  have hreal (i : Fin k) : Complex.reCLM.toLinearMap.comp
      (((b i).val.extendRCLike (𝕜 := ℂ)).restrictScalars ℝ) = (b i).val := by
    apply LinearMap.ext
    intro x
    exact Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x
  apply complex_independent_of_generic_real_conormals (S : Set (Affine n)) hS
    (fun i => (b i).val.extendRCLike)
  · intro i x hx
    exact (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x).trans
      ((Submodule.mem_dualAnnihilator _).mp (b i).property x hx)
  · have hb := submodule_basis_independent S.dualAnnihilator b
    simpa only [hreal] using hb

lemma real_conormal_basis_vanishing_iff {n k : ℕ}
    (S : Submodule ℝ (Affine n))
    (b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator) (x : Affine n) :
    x ∈ S ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator _).mp (b i).property x hx
  · intro h
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := S)]
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro Q hQ
    let q : S.dualAnnihilator := ⟨Q,hQ⟩
    have heq := b.sum_repr q
    have heq' := congrArg (fun v : S.dualAnnihilator => v.val x) heq
    simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower,
      LinearMap.sum_apply,LinearMap.smul_apply,h,smul_zero,Finset.sum_const_zero] using heq'.symm

theorem generic_tangent_complex_normal_form {n : ℕ}
    (S : Submodule ℝ (Affine n)) (hS : Submodule.span ℂ (S : Set (Affine n)) = ⊤) :
    ∃ r : ℕ, ∃ e : Affine n ≃L[ℂ]
      (Affine r × Affine (Module.finrank ℝ S.dualAnnihilator)),
      r + Module.finrank ℝ S.dualAnnihilator = n ∧
      ∀ x, x ∈ S ↔ ∀ i, ((e x).2 i).im = 0 := by
  let _ : Module.Free ℝ ↥S.dualAnnihilator := Module.Free.of_divisionRing ℝ ↥S.dualAnnihilator
  let k := Module.finrank ℝ S.dualAnnihilator
  let b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator := Module.finBasis ℝ ↥S.dualAnnihilator
  let l : Fin k → Module.Dual ℂ (Affine n) := fun i => (b i).val.extendRCLike
  have hi : LinearIndependent ℂ l := real_conormal_basis_complex_independent S hS b
  let L : Affine n →L[ℂ] Affine k := (LinearMap.pi l).toContinuousLinearMap
  let A : Affine n →L[ℂ] Affine k := Complex.I • L
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨x,hx⟩ := independent_functionals_surjective l hi ((-Complex.I) • y)
    refine ⟨x,?_⟩
    change Complex.I • L x = y
    change L x = (-Complex.I) • y at hx
    rw [hx,smul_smul]
    simp
  obtain ⟨e,he⟩ := exists_scalar_continuousLinearEquiv_prod_ker A hA
  let r := Module.finrank ℂ (LinearMap.ker A.toLinearMap)
  let c : LinearMap.ker A.toLinearMap ≃L[ℂ] Affine r :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [r,Affine])
  let f := (e.trans ((ContinuousLinearEquiv.refl ℂ (Affine k)).prodCongr c)).trans
    (ContinuousLinearEquiv.prodComm ℂ (Affine k) (Affine r))
  have hf (x : Affine n) : (f x).2 = A x := he x
  have hdim : r+k=n := by
    have hh := f.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_prod,Affine,Module.finrank_pi,
      Fintype.card_fin] using hh.symm
  refine ⟨r,f,hdim,?_⟩
  intro x
  have hx (i : Fin k) : ((f x).2 i).im = (b i).val x := by
    rw [hf]
    change (Complex.I * l i x).im = (b i).val x
    simp only [Complex.I_mul_im]
    exact Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x
  simp only [hx]
  exact real_conormal_basis_vanishing_iff S b x
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NashCellGeometricRank
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

theorem real_parametric_span_eq_chart_of_rank_ge {d m N : ℕ}
    (F : (Fin m → ℂ) → (Fin N → ℂ))
    (G : (Fin N → ℂ) → (Fin m → ℂ))
    (q : (Fin d → ℝ) → (Fin N → ℂ)) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Fin m → ℂ)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ (range (fderiv ℝ q x)) =
      LinearMap.range (fderiv ℂ F 0).toLinearMap := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  apply complex_tangent_eq_of_rank_ge (fderiv ℝ q x).toLinearMap
    (LinearMap.range (fderiv ℂ F 0).toLinearMap)
  · exact chart_tangent_finrank F G hF (hF0 ▸ hG) hGF
  · intro v
    have hv := real_derivative_mem_chart_tangent F G q (hG0 ▸ hF) hG hq hFG v
    change fderiv ℝ q x v ∈ _
    simpa only [hG0] using hv
  · rw [matrix_rank_eq_complex_tangent_dimension]
    rwa [coordinate_derivative_rank q hq] at hr

end

open Set Filter Topology MeasureTheory

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InjectiveConormalFinrank
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

theorem chart_tangent_identities {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x)
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q) :
    G (q x) = 0 ∧
    (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ ∧
    ((fderiv ℂ F 0).restrictScalars ℝ).comp (fderiv ℝ (G ∘ q) x) = fderiv ℝ q x ∧
    Function.Injective (fderiv ℂ F 0) := by
  have hG0 : G (q x) = 0 := by
    simpa only [Function.comp_apply,hF0,Function.id_def] using hGF.eq_of_nhds
  have hg : AnalyticAt ℂ G (F 0) := hF0 ▸ hG
  have hid := (hg.differentiableAt.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hGF.symm
  have hi : (fderiv ℂ G (q x)).comp (fderiv ℂ F 0) = ContinuousLinearMap.id ℂ _ := by
    simpa only [hF0] using hid.unique (hasFDerivAt_id (0 : Affine m))
  refine ⟨hG0,hi,?_,?_⟩
  · have hr : DifferentiableAt ℝ (G ∘ q) x := hG.differentiableAt.restrictScalars ℝ |>.comp x hq
    have hf : AnalyticAt ℂ F ((G ∘ q) x) := by simpa only [Function.comp_apply,hG0] using hF
    have hh := (hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hr.hasFDerivAt
    have he := hh.congr_of_eventuallyEq hFG.symm
    simpa only [Function.comp_apply,hG0] using he.fderiv.symm
  · intro a b hab
    have hh := congrArg (fderiv ℂ G (q x)) hab
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

theorem chart_parametric_generic {d m N : ℕ}
    (F : Affine m → Affine N) (G : Affine N → Affine m)
    (q : (Fin d → ℝ) → Affine N) {x : Fin d → ℝ}
    (hF0 : F 0 = q x) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G (q x))
    (hq : DifferentiableAt ℝ q x) (hqi : Function.Injective (fderiv ℝ q x))
    (hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id)
    (hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q)
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (G ∘ q) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x)) = ⊤ := by
  obtain ⟨hG0,hi,hd,hFi⟩ := chart_tangent_identities F G q hF0 hF hG hq hGF hFG
  have hspan := real_parametric_span_eq_chart_of_rank_ge F G q hF0 hF hG hq hGF hFG hr
  have hder : fderiv ℝ (G ∘ q) x = ((fderiv ℂ G (q x)).restrictScalars ℝ).comp (fderiv ℝ q x) :=
    ((hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x hq.hasFDerivAt).fderiv
  refine ⟨?_,?_⟩
  · intro a b hab
    apply hqi
    rw [← hd]
    exact congrArg ((fderiv ℂ F 0).restrictScalars ℝ) hab
  · let W := Submodule.span ℂ (range (fderiv ℝ (G ∘ q) x))
    have hle : Submodule.span ℂ (range (fderiv ℝ q x)) ≤
        W.comap (fderiv ℂ G (q x)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v,rfl⟩
      change fderiv ℂ G (q x) (fderiv ℝ q x v) ∈ W
      have he : fderiv ℂ G (q x) (fderiv ℝ q x v) = fderiv ℝ (G ∘ q) x v := by
        rw [hder]; rfl
      rw [he]
      exact Submodule.subset_span (mem_range_self v)
    apply top_unique
    intro v _
    have hv : fderiv ℂ F 0 v ∈ Submodule.span ℂ (range (fderiv ℝ q x)) := by
      rw [hspan]; exact ⟨v,rfl⟩
    have hh := hle hv
    change fderiv ℂ G (q x) (fderiv ℂ F 0 v) ∈ W at hh
    simpa only [← ContinuousLinearMap.comp_apply,hi,ContinuousLinearMap.id_apply] using hh

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OldOffsetOldPosition
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

theorem NashNormalCoordinates.graph_germ_at {d m : ℕ}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine m} {a x : Fin d → ℝ}
    (c : NashNormalCoordinates B q a) (hx : x ∈ c.parameters.source)
    (hxb : c.parameters x ∈ ball 0 c.radius) :
    ∀ᶠ y in 𝓝 x, c.parameters y ∈ ball 0 c.radius ∧
      c.realCoordinates (q y-q a) = (c.parameters y,c.graph (c.parameters y)) := by
  have hs := c.parameters.open_source.mem_nhds hx
  have hb := (c.parameters.continuousAt hx).preimage_mem_nhds (isOpen_ball.mem_nhds hxb)
  filter_upwards [hs,hb] with y hy hyb
  refine ⟨hyb,?_⟩
  change complexGraphRealEquiv _ _ (c.coordinates (q y-q a)) = _
  simpa only [c.parameters.left_inv hy] using c.graph_identity (c.parameters y) hyb

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

 theorem oldOffset_projection_germ (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) :
    (fun y => c.oldOffset (c.chart.projection (q y-q c.center))) =ᶠ[𝓝 x] fun _ => 0 := by
  have hg := c.normal.graph_germ_at hgood.1 (ball_subset_ball c.graphRadius_le hgood.2.1)
  have h0 : c.chart.projection (q c.center-q c.center) = 0 := by rw [sub_self,map_zero]
  filter_upwards [hg] with y hy
  simp only [h0,sub_zero] at hy
  simp only [oldOffset,oldParameter,hy.2,sub_self]
end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectionTangentGeneric
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

theorem projection_inverse_germ (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) :
    (fun y => c.chart.inverse (c.chart.projection (q y-q c.center))) =ᶠ[𝓝 x] q := by
  have hs := c.normal.parameters.open_source.mem_nhds hgood.1
  have hb := (c.normal.parameters.continuousAt hgood.1).preimage_mem_nhds
    (isOpen_ball.mem_nhds hgood.2.1)
  have h0 : c.chart.projection (q c.center-q c.center) = 0 := by rw [sub_self,map_zero]
  filter_upwards [hs,hb] with y hy hyb
  have hgr := c.normal.graph_identity (c.normal.parameters y) (ball_subset_ball c.graphRadius_le hyb)
  simp only [c.normal.parameters.left_inv hy,h0,sub_zero] at hgr
  have hpos : c.oldPosition (c.normal.parameters y) = c.chart.projection (q y-q c.center) := by
    apply c.normal.realCoordinates.injective
    rw [oldPosition,ContinuousLinearEquiv.apply_symm_apply]
    exact hgr.symm
  rw [← hpos]
  simpa only [oldPosition,c.normal.parameters.left_inv hy] using (c.graph_boundary _ hyb).2.2

theorem projection_tangent_generic (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Function.Injective (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x) ∧
    Submodule.span ℂ (range (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x)) = ⊤ := by
  let a := c.oldPosition (c.normal.parameters x)
  let F := fun z => c.chart.inverse (z+a)
  let G := fun y => c.chart.projection (y-q c.center)-a
  have ha : ‖complexRealEquiv m a‖ < c.chart.radius := (c.graph_boundary _ hgood.2.1).2.1
  have hF0 : F 0 = q x := by simpa only [F,zero_add] using c.oldPosition_inverse hgood
  have hF : AnalyticAt ℂ F 0 := by
    have hfa : AnalyticAt ℂ c.chart.inverse ((0 : Affine m)+a) := by
      simpa only [zero_add] using c.chart.inverse_analytic a ha
    exact hfa.comp (f := fun z : Affine m => z+a) (x := 0) (analyticAt_id.add analyticAt_const)
  have hG : AnalyticAt ℂ G (q x) :=
    ((c.chart.projection.analyticAt _).comp (analyticAt_id.sub analyticAt_const)).sub analyticAt_const
  have hT : IsOpen {z : Affine m | ‖complexRealEquiv m (z+a)‖ < c.chart.radius} :=
    isOpen_lt (((complexRealEquiv m).continuous.comp (continuous_id.add continuous_const)).norm) continuous_const
  have hGF : (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id := by
    filter_upwards [hT.mem_nhds (by simpa using ha)] with z hz
    change c.chart.projection (c.chart.inverse (z+a)-q c.center)-a = z
    rw [c.chart.left_inverse (z+a) hz,add_sub_cancel_right]
  have hFG : (F ∘ G ∘ q) =ᶠ[𝓝 x] q := by
    simpa only [F,G,Function.comp_def,sub_add_cancel] using c.projection_inverse_germ hgood
  have ht := chart_parametric_generic F G q hF0 hF hG hq hqi hGF hFG hr
  have hd : fderiv ℝ (G ∘ q) x = fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x := by
    have hh := (((c.chart.projection.restrictScalars ℝ).differentiableAt.comp x
      (hq.sub_const (q c.center))).hasFDerivAt.sub_const a).fderiv
    exact hh
  rwa [hd] at ht
end NashBoundaryChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GenericSurjectiveRealNormal
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
namespace Release061.NashBoundaryChart
open Set Filter Topology Metric
open scoped Classical
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

 theorem oldOffset_hasFDerivAt (c : NashBoundaryChart (m := m) U V B q) {s}
    (hs : s ∈ ball 0 c.graphRadius) :
    HasFDerivAt c.oldOffset (c.oldOffsetDerivative s) (c.oldPosition s) := by
  have hC := c.normal.realCoordinates.toContinuousLinearMap.hasFDerivAt (x := c.oldPosition s)
  have hP := (ContinuousLinearMap.fst ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hQ := (ContinuousLinearMap.snd ℝ _ _).hasFDerivAt.comp (c.oldPosition s) hC
  have hφ := (c.normal.graph_analytic s (ball_subset_ball c.graphRadius_le hs)).differentiableAt.hasFDerivAt
  have hφ' : HasFDerivAt c.normal.graph (fderiv ℝ c.normal.graph s)
      (c.oldParameter (c.oldPosition s)) := by simpa only [oldParameter_oldPosition] using hφ
  exact hQ.sub (hφ'.comp (c.oldPosition s) hP)

 theorem oldOffsetDerivative_surjective (c : NashBoundaryChart (m := m) U V B q) (s) :
    Function.Surjective (c.oldOffsetDerivative s) := by
  intro v
  refine ⟨c.normal.realCoordinates.symm (0,v),?_⟩
  change (c.normal.realCoordinates (c.normal.realCoordinates.symm (0,v))).2 -
    fderiv ℝ c.normal.graph s (c.normal.realCoordinates (c.normal.realCoordinates.symm (0,v))).1 = v
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_zero,sub_zero]

theorem oldOffsetDerivative_generic (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Submodule.span ℂ ((LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap) : Set (Affine m)) = ⊤ := by
  let f : (Fin d → ℝ) → Affine m := fun y => c.chart.projection (q y-q c.center)
  have hf : DifferentiableAt ℝ f x := (c.chart.projection.restrictScalars ℝ).differentiableAt.comp x (hq.sub_const (q c.center))
  have hD : HasFDerivAt c.oldOffset (c.oldOffsetDerivative (c.normal.parameters x)) (f x) := by
    dsimp only [f]
    rw [← c.oldPosition_projection hgood]
    exact c.oldOffset_hasFDerivAt hgood.2.1
  have hz : (c.oldOffsetDerivative (c.normal.parameters x)).comp (fderiv ℝ f x) = 0 :=
    ((hD.comp x hf.hasFDerivAt).congr_of_eventuallyEq (c.oldOffset_projection_germ hgood).symm).unique (hasFDerivAt_const (0 : Fin c.normal.normalDim → ℝ) x)
  have hle : range (fderiv ℝ f x) ⊆ ((LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap) : Set (Affine m)) := by
    rintro _ ⟨v,rfl⟩
    change c.oldOffsetDerivative (c.normal.parameters x) (fderiv ℝ f x v) = 0
    exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin c.normal.normalDim → ℝ) => L v) hz
  have hgen := (c.projection_tangent_generic hgood hq hqi hr).2
  apply top_unique
  rw [← hgen]
  exact Submodule.span_mono hle
end Release061.NashBoundaryChart

namespace Release061
open Set Filter Topology Flatten
open scoped Classical

theorem real_surjection_normal_factor {r l k : ℕ}
    (M : (Affine r × Affine l) →L[ℝ] (Fin k → ℝ))
    (hM : Function.Surjective M)
    (hker : ∀ z, M z = 0 ↔ Flatten.imaginaryPart l z.2 = 0) :
    ∃ L : (Fin l → ℝ) ≃L[ℝ] (Fin k → ℝ),
      ∀ z, M z = L (Flatten.imaginaryPart l z.2) := by
  let j : (Fin l → ℝ) →L[ℝ] (Affine r × Affine l) :=
    (ContinuousLinearMap.inr ℝ (Affine r) (Affine l)).comp
      (((Complex.I • ContinuousLinearMap.id ℂ (Affine l)).restrictScalars ℝ).comp (Flatten.realEmbedding l))
  have hj (v : Fin l → ℝ) : Flatten.imaginaryPart l (j v).2 = v := by
    ext i
    simp [j,Flatten.imaginaryPart,Flatten.realEmbedding]
  let L := M.comp j
  have hf (z : Affine r × Affine l) : M z = L (Flatten.imaginaryPart l z.2) := by
    have hz : M (z-j (Flatten.imaginaryPart l z.2)) = 0 := by
      apply (hker _).mpr
      change Flatten.imaginaryPart l (z.2-(j (Flatten.imaginaryPart l z.2)).2) = 0
      rw [map_sub,hj,sub_self]
    exact sub_eq_zero.mp (by simpa only [map_sub,L,ContinuousLinearMap.comp_apply] using hz)
  have hi : Function.Injective L := by
    intro u v huv
    apply sub_eq_zero.mp
    have hz : M (j (u-v)) = 0 := by change L (u-v)=0; rw [map_sub,huv,sub_self]
    simpa only [hj] using (hker _).mp hz
  have hs : Function.Surjective L := by
    intro y
    obtain ⟨z,hz⟩ := hM y
    exact ⟨Flatten.imaginaryPart l z.2,by rw [← hf,hz]⟩
  exact ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv,hf⟩

theorem generic_surjective_real_normal_form {m k : ℕ}
    (D : Affine m →L[ℝ] (Fin k → ℝ)) (hD : Function.Surjective D)
    (hgen : Submodule.span ℂ ((LinearMap.ker D.toLinearMap) : Set (Affine m)) = ⊤) :
    ∃ (r l : ℕ) (e : Affine m ≃L[ℂ] (Affine r × Affine l))
      (L : (Fin l → ℝ) ≃L[ℝ] (Fin k → ℝ)),
      r+l=m ∧ l=k ∧ ∀ z, D (e.symm z) = L (Flatten.imaginaryPart l z.2) := by
  obtain ⟨r,e,hdim,hker⟩ := generic_tangent_complex_normal_form (LinearMap.ker D.toLinearMap) hgen
  let l := Module.finrank ℝ (LinearMap.ker D.toLinearMap).dualAnnihilator
  let M := D.comp (e.symm.toContinuousLinearMap.restrictScalars ℝ)
  have hM : Function.Surjective M := hD.comp e.symm.surjective
  have he : ∀ z, M z = 0 ↔ Flatten.imaginaryPart l z.2 = 0 := by
    intro z
    change e.symm z ∈ LinearMap.ker D.toLinearMap ↔ _
    rw [hker,ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨fun h => funext h,fun h i => congrFun h i⟩
  obtain ⟨L,hL⟩ := real_surjection_normal_factor M hM he
  have hlk : l=k := by simpa only [Module.finrank_pi,Fintype.card_fin] using L.toLinearEquiv.finrank_eq
  exact ⟨r,l,e,L,hdim,hlk,hL⟩
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OffsetDerivative
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
variable {E S V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [CompleteSpace E] [CompleteSpace S] [CompleteSpace V]

theorem offset_coordinate_local_inverse (C : E ≃L[ℝ] (S × V))
    (φ : S → V) {s : S} (hφ : AnalyticAt ℝ φ s) :
    ∃ e : OpenPartialHomeomorph E (S × V),
      (e : E → S × V) = (fun z => let u := C (z+C.symm (s,φ s)); (u.1,u.2-φ u.1)) ∧
      (0 : E) ∈ e.source ∧ e 0 = (s,0) ∧ AnalyticAt ℝ e.symm (s,0) ∧
      AnalyticAt ℝ e 0 := by
  let a := C.symm (s,φ s)
  let f : E → S × V := fun z => let u := C (z+a); (u.1,u.2-φ u.1)
  have hCa : C ((0 : E)+a) = (s,φ s) := by simp only [zero_add,a,C.apply_symm_apply]
  have hf0 : f 0 = (s,0) := by simp only [f,hCa,sub_self]
  have hC : AnalyticAt ℝ (fun z : E => C (z+a)) 0 :=
    (C.toContinuousLinearMap.analyticAt _).comp (analyticAt_id.add analyticAt_const)
  have hφ' : AnalyticAt ℝ φ (C ((0 : E)+a)).1 := by simpa only [hCa] using hφ
  have hPa : AnalyticAt ℝ (fun z : E => (C (z+a)).1) 0 := analyticAt_fst.comp hC
  have hQa : AnalyticAt ℝ (fun z : E => (C (z+a)).2) 0 := analyticAt_snd.comp hC
  have hf : AnalyticAt ℝ f 0 :=
    hPa.prod (hQa.sub (hφ'.comp (f := fun z : E => (C (z+a)).1) (x := 0) hPa))
  let L := C.trans (graphOffsetDifferentialEquiv (fderiv ℝ φ s))
  have hCd : HasFDerivAt (fun z : E => C (z+a)) C.toContinuousLinearMap 0 :=
    C.toContinuousLinearMap.hasFDerivAt.comp 0 ((hasFDerivAt_id 0).add_const a)
  have hP := hasFDerivAt_fst.comp 0 hCd
  have hQ := hasFDerivAt_snd.comp 0 hCd
  have hφd : HasFDerivAt φ (fderiv ℝ φ s) (C ((0 : E)+a)).1 := by
    simpa only [hCa] using hφ.differentiableAt.hasFDerivAt
  have hd : HasFDerivAt f (L : E →L[ℝ] (S × V)) 0 := by
    convert hP.prodMk (hQ.sub (hφd.comp 0 hP)) using 1 <;> rfl
  obtain ⟨e,he,hes,hea⟩ := real_analytic_local_inverse hf L hd
  exact ⟨e,he,hes,by simpa only [he] using hf0,by simpa only [hf0] using hea,he.symm ▸ hf⟩
end

open Set Filter Topology Metric
open scoped Classical

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem scaling_chart_oai (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    Nonempty (NashBoundaryScalingChart c x) := by
  obtain ⟨r,l,e,L,hd,hl,hL⟩ := generic_surjective_real_normal_form
    (c.oldOffsetDerivative (c.normal.parameters x)) (c.oldOffsetDerivative_surjective _)
    (c.oldOffsetDerivative_generic hgood hq hqi hr)
  let C : (Affine r × Affine l) ≃L[ℝ] _ :=
    ((e.symm.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv).trans c.normal.realCoordinates
  obtain ⟨T,hT,hTs,hT0,hTin,hTa⟩ := offset_coordinate_local_inverse C c.normal.graph
    (c.normal.graph_analytic (c.normal.parameters x) (ball_subset_ball c.graphRadius_le hgood.2.1))
  refine ⟨⟨r,l,hd,hl,e,L,hL,T,?_,hTs,hT0,hTin,hTa⟩⟩
  intro z
  rw [hT]
  change (c.oldParameter (e.symm (z+e (c.oldPosition (c.normal.parameters x)))),
    c.oldOffset (e.symm (z+e (c.oldPosition (c.normal.parameters x))))) = _
  rw [map_add,e.symm_apply_apply]
end NashBoundaryChart

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.NashBoundaryChart.scaling_chart_oai := @OAI.Release061.NashBoundaryChart.scaling_chart_oai
