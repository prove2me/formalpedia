-- Prove2me | solution 1 for OAI.HochschildNormalPart.functionalModel_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:44:40.108961+00:00
-- url     : https://prove2.me/submissions/9462787a-4375-4458-a7e7-f7e21e704155

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [CompleteSpace X]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

end HochschildNormalPart

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma coefficient_sum (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (η ξ : WithLp 2 (H×K)) :
    coefficient (sumRepresentation π ρ) η ξ=
      coefficient π η.fst ξ.fst+coefficient ρ η.snd ξ.snd := by
  ext a; rfl
end HochschildNormalPart
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
namespace HochschildPositiveDecomposition
universe u
variable {M : Type u} [CStarAlgebra M]

lemma norm_pair_shift [Nontrivial M] (a : selfAdjoint M) (t : ℝ) :
    ‖a‖ + |t| ≤ ‖(a + t • (1 : selfAdjoint M), -a + t • (1 : selfAdjoint M))‖ := by
  let C := ‖(a + t • (1 : selfAdjoint M), -a + t • (1 : selfAdjoint M))‖
  have h₁ : ‖(a : M) + algebraMap ℝ M t‖ ≤ C := by
    rw [Algebra.algebraMap_eq_smul_one]
    change ‖(a : M) + t • (1:M)‖ ≤ max ‖(a : M)+t • (1:M)‖ ‖-(a : M)+t • (1:M)‖
    exact le_max_left _ _
  have h₂ : ‖-(a : M) + algebraMap ℝ M t‖ ≤ C := by
    rw [Algebra.algebraMap_eq_smul_one]
    change ‖-(a : M) + t • (1:M)‖ ≤ max ‖(a : M)+t • (1:M)‖ ‖-(a : M)+t • (1:M)‖
    exact le_max_right _ _
  have hs (r : ℝ) (hr : r ∈ spectrum ℝ (a : M)) : |r+t| ≤ C ∧ |-r+t| ≤ C := by
    constructor
    · have h := spectrum.norm_le_norm_of_mem (spectrum.add_mem_add_iff.mpr hr : r+t ∈ spectrum ℝ (algebraMap ℝ M t+(a : M)))
      exact h.trans (by simpa [add_comm] using h₁)
    · have hn : -r ∈ spectrum ℝ (-(a : M)) := by rw [← spectrum.neg_eq]; exact Set.neg_mem_neg.mpr hr
      have h := spectrum.norm_le_norm_of_mem (spectrum.add_mem_add_iff.mpr hn : -r+t ∈ spectrum ℝ (algebraMap ℝ M t+ -(a : M)))
      exact h.trans (by simpa [sub_eq_add_neg,add_comm] using h₂)
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a.property with ha|ha
  · obtain ⟨h₁,h₂⟩ := hs ‖a‖ ha
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]; linarith [le_abs_self (‖a‖+t)]
    · rw [abs_of_nonpos ht]; linarith [neg_le_abs (-‖a‖+t)]
  · obtain ⟨h₁,h₂⟩ := hs (-‖a‖) ha
    rcases le_total 0 t with ht|ht
    · rw [abs_of_nonneg ht]; linarith [le_abs_self (-(-‖a‖)+t)]
    · rw [abs_of_nonpos ht]; linarith [neg_le_abs (-‖a‖+t)]

def shiftEmbedding : selfAdjoint M × ℝ →ₗ[ℝ] selfAdjoint M × selfAdjoint M where
  toFun p := (p.1+p.2 • 1,-p.1+p.2 • 1)
  map_add' p q := by ext <;> simp <;> module
  map_smul' r p := by ext <;> simp <;> module

lemma shiftEmbedding_injective [Nontrivial M] : Function.Injective (shiftEmbedding (M := M)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  have h := norm_pair_shift p.1 p.2
  have he : shiftEmbedding p=0 := hp
  change ‖p.1‖+|p.2|≤‖shiftEmbedding p‖ at h
  rw [he,norm_zero] at h
  have hp₁ : p.1=0 := norm_eq_zero.mp (by linarith [norm_nonneg p.1,abs_nonneg p.2])
  have hp₂ : p.2=0 := abs_eq_zero.mp (by linarith [norm_nonneg p.1,abs_nonneg p.2])
  exact Prod.ext hp₁ hp₂

lemma exists_pair_extension [Nontrivial M] (l : StrongDual ℝ (selfAdjoint M)) :
    ∃ g : StrongDual ℝ (selfAdjoint M × selfAdjoint M),
      ‖g‖ ≤ ‖l‖ ∧ g (1,1)=‖l‖ ∧ ∀ a, g (a,-a)=l a := by
  let j := LinearEquiv.ofInjective (shiftEmbedding (M := M)) shiftEmbedding_injective
  let L : selfAdjoint M × ℝ →ₗ[ℝ] ℝ := l.toLinearMap.coprod (‖l‖ • LinearMap.id)
  let L' := L.comp j.symm.toLinearMap
  have hbound (p : (shiftEmbedding (M := M)).range) : ‖L' p‖ ≤ ‖l‖*‖p‖ := by
    obtain ⟨q,rfl⟩ := j.surjective p
    change ‖L (j.symm (j q))‖ ≤ ‖l‖*‖shiftEmbedding q‖
    rw [j.symm_apply_apply]
    change ‖l q.1+‖l‖*q.2‖ ≤ ‖l‖*‖shiftEmbedding q‖
    calc
      _ ≤ ‖l q.1‖+‖‖l‖*q.2‖ := norm_add_le _ _
      _ ≤ ‖l‖*‖q.1‖+‖l‖*|q.2| := by simpa [abs_of_nonneg (norm_nonneg l)] using add_le_add (l.le_opNorm q.1) (le_refl ‖‖l‖*q.2‖)
      _ = ‖l‖*(‖q.1‖+|q.2|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pair_shift q.1 q.2) (norm_nonneg l)
  let F := L'.mkContinuous ‖l‖ hbound
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq (shiftEmbedding (M := M)).range F
  refine ⟨g,?_,?_,?_⟩
  · rw [hgn]; exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg l) hbound
  · have h := hg (j (0,1))
    change g (shiftEmbedding (0,1))=L (j.symm (j (0,1))) at h
    rw [j.symm_apply_apply] at h
    simpa [L,shiftEmbedding] using h
  · intro a
    have h := hg (j (a,0))
    change g (shiftEmbedding (a,0))=L (j.symm (j (a,0))) at h
    rw [j.symm_apply_apply] at h
    simpa [L,shiftEmbedding] using h

section Ordered
variable [PartialOrder M] [StarOrderedRing M]

lemma norm_orderUnit_sub (a : selfAdjoint M) (ha : 0≤(a:M)) {r : ℝ}
    (hr : 0≤r) (har : ‖a‖≤r) : ‖r • (1:selfAdjoint M)-a‖≤r := by
  change ‖r • (1:M)-(a:M)‖≤r
  have hle : (a:M)≤algebraMap ℝ M r := by
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (a:M) hr ha).mp har
  rw [Algebra.algebraMap_eq_smul_one] at hle
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hr (sub_nonneg.mpr hle)).mpr (by
    rw [Algebra.algebraMap_eq_smul_one]
    exact sub_le_self _ ha)

lemma pair_nonneg (g : StrongDual ℝ (selfAdjoint M × selfAdjoint M)) {C : ℝ}
    (hC : 0≤C) (hgn : ‖g‖≤C) (hg1 : g (1,1)=C)
    (a b : selfAdjoint M) (ha : 0≤(a:M)) (hb : 0≤(b:M)) : 0≤g (a,b) := by
  let r := ‖(a,b)‖
  have hr : 0≤r := norm_nonneg _
  have hn : ‖r • (1,1)-(a,b)‖ ≤ r := by
    change max ‖r • (1:selfAdjoint M)-a‖ ‖r • (1:selfAdjoint M)-b‖≤r
    exact max_le (norm_orderUnit_sub a ha hr (le_max_left _ _))
      (norm_orderUnit_sub b hb hr (le_max_right _ _))
  have h := (le_abs_self (g (r • (1,1)-(a,b)))).trans
    ((g.le_opNorm _).trans (mul_le_mul hgn hn (norm_nonneg _) hC))
  rw [map_sub,map_smul,hg1] at h
  change r*C-g (a,b)≤C*r at h
  nlinarith

lemma exists_real_positive_difference [Nontrivial M] (l : StrongDual ℝ (selfAdjoint M)) :
    ∃ p q : StrongDual ℝ (selfAdjoint M),
      (∀ a : selfAdjoint M, 0≤(a:M) → 0≤p a) ∧ (∀ a : selfAdjoint M, 0≤(a:M) → 0≤q a) ∧
      (∀ a, l a=p a-q a) ∧ p 1≤‖l‖ ∧ q 1≤‖l‖ := by
  obtain ⟨g,hgn,hg1,hgl⟩ := exists_pair_extension l
  let p := g.comp (ContinuousLinearMap.inl ℝ (selfAdjoint M) (selfAdjoint M))
  let q := g.comp (ContinuousLinearMap.inr ℝ (selfAdjoint M) (selfAdjoint M))
  refine ⟨p,q,?_,?_,?_,?_,?_⟩
  · intro a ha; exact pair_nonneg g (norm_nonneg l) hgn hg1 a 0 ha (by simp)
  · intro a ha; exact pair_nonneg g (norm_nonneg l) hgn hg1 0 a (by simp) ha
  · intro a
    rw [← hgl]
    change g (a,-a)=g (a,0)-g (0,a)
    rw [← map_sub]; congr 1; simp
  · have h := (le_abs_self (g (1,0))).trans (g.le_opNorm (1,0))
    have hn : ‖((1:selfAdjoint M), (0:selfAdjoint M))‖≤1 := by
      change max ‖(1:M)‖ ‖(0:M)‖≤1
      simp
    exact h.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg g)).trans (by simpa using hgn))
  · have h := (le_abs_self (g (0,1))).trans (g.le_opNorm (0,1))
    have hn : ‖((0:selfAdjoint M), (1:selfAdjoint M))‖≤1 := by
      change max ‖(0:M)‖ ‖(1:M)‖≤1
      simp
    exact h.trans ((mul_le_mul_of_nonneg_left hn (norm_nonneg g)).trans (by simpa using hgn))

end Ordered

def complexify (l : selfAdjoint M →ₗ[ℝ] ℝ) : M →ₗ[ℂ] ℂ where
  toFun a := (l (ℜ a):ℂ)+Complex.I*(l (ℑ a):ℂ)
  map_add' a b := by simp; ring
  map_smul' c a := by
    apply Complex.ext <;> simp [realPart_smul,imaginaryPart_smul]

@[simp] lemma complexify_apply (l : selfAdjoint M →ₗ[ℝ] ℝ) (a : M) :
    complexify l a=(l (ℜ a):ℂ)+Complex.I*(l (ℑ a):ℂ) := rfl

@[simp] lemma complexify_selfAdjoint (l : selfAdjoint M →ₗ[ℝ] ℝ) (a : selfAdjoint M) :
    complexify l (a:M)=(l a:ℂ) := by
  have h : ℜ (a:M)=a := Subtype.ext a.property.coe_realPart
  simp [h,a.property.imaginaryPart]

section Ordered
variable [PartialOrder M] [StarOrderedRing M]
open scoped ComplexOrder

def complexifyPositive (l : selfAdjoint M →ₗ[ℝ] ℝ)
    (hl : ∀ a : selfAdjoint M,0≤(a:M) → 0≤l a) : M →ₚ[ℂ] ℂ where
  toLinearMap := complexify l
  monotone' := by
    intro a b hab
    change complexify l a≤complexify l b
    rw [← sub_nonneg,← map_sub]
    have hp := sub_nonneg.mpr hab
    have hs : IsSelfAdjoint (b-a) := .of_nonneg hp
    have he := complexify_selfAdjoint l ⟨b-a,hs⟩
    rw [he]
    exact_mod_cast hl ⟨b-a,hs⟩ hp

@[simp] lemma complexifyPositive_apply (l : selfAdjoint M →ₗ[ℝ] ℝ)
    (hl : ∀ a : selfAdjoint M,0≤(a:M) → 0≤l a) (a : M) :
    complexifyPositive l hl a=complexify l a := rfl

end Ordered

def realRestriction (φ : StrongDual ℂ M) : StrongDual ℝ (selfAdjoint M) :=
  Complex.reCLM.comp ((φ.restrictScalars ℝ).comp (selfAdjoint.submodule ℝ M).subtypeL)

def imagRestriction (φ : StrongDual ℂ M) : StrongDual ℝ (selfAdjoint M) :=
  Complex.imCLM.comp ((φ.restrictScalars ℝ).comp (selfAdjoint.submodule ℝ M).subtypeL)

@[simp] lemma realRestriction_apply (φ : StrongDual ℂ M) (a : selfAdjoint M) :
    realRestriction φ a=(φ (a:M)).re := rfl
@[simp] lemma imagRestriction_apply (φ : StrongDual ℂ M) (a : selfAdjoint M) :
    imagRestriction φ a=(φ (a:M)).im := rfl

lemma realRestriction_norm (φ : StrongDual ℂ M) : ‖realRestriction φ‖≤‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro a
  exact (Complex.abs_re_le_norm _).trans (φ.le_opNorm (a:M))
lemma imagRestriction_norm (φ : StrongDual ℂ M) : ‖imagRestriction φ‖≤‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
  intro a
  exact (Complex.abs_im_le_norm _).trans (φ.le_opNorm (a:M))

lemma real_imag_restriction_decomposition (φ : StrongDual ℂ M) (a : M) :
    φ a=complexify (realRestriction φ).toLinearMap a+
      Complex.I*complexify (imagRestriction φ).toLinearMap a := by
  have h := congrArg φ (realPart_add_I_smul_imaginaryPart a)
  rw [map_add,map_smul] at h
  rw [← h]
  simp only [complexify_apply,ContinuousLinearMap.coe_coe,realRestriction_apply,imagRestriction_apply]
  apply Complex.ext <;> simp
  ring

section Ordered
variable [PartialOrder M] [StarOrderedRing M]
open scoped ComplexOrder

theorem exists_four_positive (φ : StrongDual ℂ M) :
    ∃ ψ : Fin 4 → (M →ₚ[ℂ] ℂ), (∀ i,‖ψ i 1‖≤‖φ‖) ∧
      ∀ a,φ a=ψ 0 a-ψ 1 a+Complex.I*(ψ 2 a-ψ 3 a) := by
  classical
  obtain hsub|hnontriv := subsingleton_or_nontrivial M
  · refine ⟨0,?_,?_⟩
    · simp
    · intro a; simp [Subsingleton.elim a 0]
  let := hnontriv
  obtain ⟨p,q,hp,hq,hpr,hp1,hq1⟩ := exists_real_positive_difference (realRestriction φ)
  obtain ⟨r,s,hr,hs,hrs,hr1,hs1⟩ := exists_real_positive_difference (imagRestriction φ)
  let P := complexifyPositive p.toLinearMap hp
  let Q := complexifyPositive q.toLinearMap hq
  let R := complexifyPositive r.toLinearMap hr
  let S := complexifyPositive s.toLinearMap hs
  have hn (l : StrongDual ℝ (selfAdjoint M)) (hl : ∀ a : selfAdjoint M,0≤(a:M) → 0≤l a) :
      ‖complexifyPositive l.toLinearMap hl 1‖=l 1 := by
    change ‖complexify l.toLinearMap (1:M)‖=l 1
    have h := complexify_selfAdjoint l.toLinearMap (1:selfAdjoint M)
    change complexify l.toLinearMap (1:M)=(l 1:ℂ) at h
    rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hl 1 (by simp))]
  refine ⟨![P,Q,R,S],?_,?_⟩
  · intro i
    fin_cases i
    · exact (le_of_eq (hn p hp)).trans (hp1.trans (realRestriction_norm φ))
    · exact (le_of_eq (hn q hq)).trans (hq1.trans (realRestriction_norm φ))
    · exact (le_of_eq (hn r hr)).trans (hr1.trans (imagRestriction_norm φ))
    · exact (le_of_eq (hn s hs)).trans (hs1.trans (imagRestriction_norm φ))
  · intro a
    change φ a=P a-Q a+Complex.I*(R a-S a)
    rw [real_imag_restriction_decomposition φ a]
    simp only [P,Q,R,S,complexifyPositive_apply,complexify_apply,
      ContinuousLinearMap.coe_coe,hpr,hrs,Complex.ofReal_sub]
    ring
end Ordered
end HochschildPositiveDecomposition
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace HochschildNormalPart
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def positiveVector (ψ : M →ₚ[ℂ] ℂ) : ψ.GNS := (ψ.toPreGNS 1 : ψ.PreGNS)

lemma positiveVector_coefficient (ψ : M →ₚ[ℂ] ℂ) (a : M) :
    coefficient ψ.gnsStarAlgHom (positiveVector ψ) (positiveVector ψ) a=ψ a := by
  change ⟪(ψ.toPreGNS 1 : ψ.GNS),ψ.gnsNonUnitalStarAlgHom a (ψ.toPreGNS 1)⟫_ℂ=ψ a
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe,UniformSpace.Completion.inner_coe]
  simp [PositiveLinearMap.preGNS_inner_def]

lemma positiveVector_norm_sq (ψ : M →ₚ[ℂ] ℂ) : ‖positiveVector ψ‖^2=‖ψ 1‖ := by
  have hv := positiveVector_coefficient ψ (1:M)
  simp only [coefficient_apply,map_one] at hv
  change ⟪positiveVector ψ,positiveVector ψ⟫_ℂ=ψ 1 at hv
  rw [inner_self_eq_norm_sq_to_K] at hv
  rw [← hv,norm_pow]
  simp

abbrev FourHilbert (ψ : Fin 4 → M →ₚ[ℂ] ℂ) :=
  WithLp 2 ((WithLp 2 ((ψ 0).GNS × (ψ 1).GNS)) ×
    (WithLp 2 ((ψ 2).GNS × (ψ 3).GNS)))

def fourRepresentation (ψ : Fin 4 → M →ₚ[ℂ] ℂ) :
    M →⋆ₐ[ℂ] (FourHilbert ψ →L[ℂ] FourHilbert ψ) :=
  sumRepresentation (sumRepresentation (ψ 0).gnsStarAlgHom (ψ 1).gnsStarAlgHom)
    (sumRepresentation (ψ 2).gnsStarAlgHom (ψ 3).gnsStarAlgHom)

def fourLeft (ψ : Fin 4 → M →ₚ[ℂ] ℂ) : FourHilbert ψ :=
  WithLp.toLp 2 (WithLp.toLp 2 (positiveVector (ψ 0),-positiveVector (ψ 1)),
    WithLp.toLp 2 (-Complex.I • positiveVector (ψ 2),Complex.I • positiveVector (ψ 3)))

def fourRight (ψ : Fin 4 → M →ₚ[ℂ] ℂ) : FourHilbert ψ :=
  WithLp.toLp 2 (WithLp.toLp 2 (positiveVector (ψ 0),positiveVector (ψ 1)),
    WithLp.toLp 2 (positiveVector (ψ 2),positiveVector (ψ 3)))

lemma four_coefficient (ψ : Fin 4 → M →ₚ[ℂ] ℂ) (a : M) :
    coefficient (fourRepresentation ψ) (fourLeft ψ) (fourRight ψ) a=
      ψ 0 a-ψ 1 a+Complex.I*(ψ 2 a-ψ 3 a) := by
  rw [fourRepresentation,coefficient_sum,add_apply]
  simp only [fourLeft,fourRight,WithLp.toLp_fst,WithLp.toLp_snd,coefficient_sum,
    add_apply,coefficient_apply,inner_neg_left,inner_smul_left]
  simp only [← coefficient_apply,positiveVector_coefficient,map_neg,Complex.conj_I]
  ring

lemma four_norm_bound (φ : StrongDual ℂ M) (ψ : Fin 4 → M →ₚ[ℂ] ℂ)
    (hψ : ∀ i,‖ψ i 1‖≤‖φ‖) : ‖fourLeft ψ‖*‖fourRight ψ‖≤4*‖φ‖ := by
  have hr : ‖fourRight ψ‖^2=‖ψ 0 1‖+‖ψ 1 1‖+(‖ψ 2 1‖+‖ψ 3 1‖) := by
    simp only [fourRight,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,
      positiveVector_norm_sq]
  have hl : ‖fourLeft ψ‖^2=‖fourRight ψ‖^2 := by
    rw [hr]
    simp only [fourLeft,WithLp.prod_norm_sq_eq_of_L2,WithLp.toLp_fst,WithLp.toLp_snd,
      norm_neg,norm_smul,Complex.norm_I,one_mul,positiveVector_norm_sq]
  have he : ‖fourLeft ψ‖=‖fourRight ψ‖ := by nlinarith [norm_nonneg (fourLeft ψ),norm_nonneg (fourRight ψ)]
  rw [he,← sq,hr]
  linarith [hψ 0,hψ 1,hψ 2,hψ 3]

attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

lemma functionalModel_nonempty (φ : StrongDual ℂ M) : Nonempty (FunctionalModel φ) := by
  obtain ⟨ψ,hψ,hφ⟩ := HochschildPositiveDecomposition.exists_four_positive φ
  refine ⟨{ H := FourHilbert ψ
            representation := fourRepresentation ψ
            leftVector := fourLeft ψ
            rightVector := fourRight ψ
            realizes := ?_
            bound := four_norm_bound φ ψ hψ }⟩
  ext a
  exact (four_coefficient ψ a).trans (hφ a).symm
end HochschildNormalPart
end
end OAI
end

theorem solution.{u} : type_of% @OAI.HochschildNormalPart.functionalModel_nonempty.{u} := @OAI.HochschildNormalPart.functionalModel_nonempty.{u}
