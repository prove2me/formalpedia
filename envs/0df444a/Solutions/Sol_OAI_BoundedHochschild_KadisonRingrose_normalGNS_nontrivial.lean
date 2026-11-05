-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.normalGNS_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:57:45.889563+00:00
-- url     : https://prove2.me/submissions/3b39b956-7197-434e-8f12-4de307389cc0

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
import Theorems.Thm_OAI_HochschildNormalPart_normalProjection_sum
import Theorems.Thm_OAI_HochschildNormalPart_functionalModel_nonempty

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

lemma coefficient_norm (η ξ : H) : ‖coefficient π η ξ‖ ≤ ‖η‖*‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro a
  calc
    _ ≤ ‖η‖*‖π a ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖*(‖π a‖*‖ξ‖) := by gcongr; exact (π a).le_opNorm ξ
    _ ≤ ‖η‖*(‖a‖*‖ξ‖) := by gcongr; exact NonUnitalStarAlgHom.norm_apply_le π a
    _ = _ := by ring

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

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma coefficient_normal_eq_of_eq
    (η ξ : H) (ζ ω : K) (h : coefficient π η ξ=coefficient ρ ζ ω) :
    coefficient π η (normalProjection e π ξ)=coefficient ρ ζ (normalProjection e ρ ω) := by
  let A : WithLp 2 (H×K) := WithLp.toLp 2 (η,ζ)
  let B : WithLp 2 (H×K) := WithLp.toLp 2 (ξ,-ω)
  have hz : coefficient (sumRepresentation π ρ) A B=0 := by
    rw [coefficient_sum]
    change coefficient π η ξ+coefficient ρ ζ (-ω)=0
    rw [map_neg,h,add_neg_cancel]
  have hn : coefficient (sumRepresentation π ρ) A B ∈ normalDual e := hz ▸ (normalDual e).zero_mem
  have hp := normalProjection_fixes_normal e (sumRepresentation π ρ) A B hn
  rw [hz,normalProjection_sum,coefficient_sum] at hp
  change coefficient π η (normalProjection e π ξ)+coefficient ρ ζ (normalProjection e ρ (-ω))=0 at hp
  rw [map_neg,map_neg] at hp
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hp)
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

attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

end HochschildNormalPart

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

def functionalModel (φ : StrongDual ℂ M) : FunctionalModel φ := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  exact Classical.choice (functionalModel_nonempty φ)

def normalPartRaw (φ : StrongDual ℂ M) : StrongDual ℂ M :=
  coefficient (functionalModel φ).representation (functionalModel φ).leftVector
    (normalProjection e (functionalModel φ).representation (functionalModel φ).rightVector)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma normalPartRaw_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    normalPartRaw e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) := by
  exact coefficient_normal_eq_of_eq e _ π _ _ η ξ (functionalModel _).realizes

lemma normalPartRaw_add (φ ψ : StrongDual ℂ M) :
    normalPartRaw e (φ+ψ)=normalPartRaw e φ+normalPartRaw e ψ := by
  let m := functionalModel φ
  let n := functionalModel ψ
  let π := sumRepresentation m.representation n.representation
  let η : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.leftVector,n.leftVector)
  let ξ : WithLp 2 (m.H×n.H) := WithLp.toLp 2 (m.rightVector,n.rightVector)
  have hc : coefficient π η ξ=φ+ψ := by
    rw [coefficient_sum]
    change coefficient m.representation m.leftVector m.rightVector+
      coefficient n.representation n.leftVector n.rightVector=φ+ψ
    rw [m.realizes,n.realizes]
  rw [← hc,normalPartRaw_coefficient,normalProjection_sum,coefficient_sum]
  rfl

lemma normalPartRaw_smul (r : ℂ) (φ : StrongDual ℂ M) :
    normalPartRaw e (r • φ)=r • normalPartRaw e φ := by
  let m := functionalModel φ
  have hc : coefficient m.representation m.leftVector (r • m.rightVector)=r • φ := by
    rw [map_smul,m.realizes]
  rw [← hc,normalPartRaw_coefficient,map_smul,map_smul]
  rfl

lemma normalPartRaw_norm (φ : StrongDual ℂ M) : ‖normalPartRaw e φ‖≤4*‖φ‖ := by
  let m := functionalModel φ
  exact (coefficient_norm _ _ _).trans
    ((mul_le_mul_of_nonneg_left ((normalVectors e m.representation).norm_starProjection_apply_le _)
      (norm_nonneg m.leftVector)).trans m.bound)

def scalarNormalPart : StrongDual ℂ M →L[ℂ] StrongDual ℂ M :=
  LinearMap.mkContinuous
    { toFun := normalPartRaw e
      map_add' := normalPartRaw_add e
      map_smul' := normalPartRaw_smul e } 4 (normalPartRaw_norm e)

@[simp] lemma scalarNormalPart_coefficient (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (η ξ : H) :
    scalarNormalPart e (coefficient π η ξ)=coefficient π η (normalProjection e π ξ) :=
  normalPartRaw_coefficient e π η ξ

lemma scalarNormalPart_fixes {φ : StrongDual ℂ M} (hφ : φ ∈ normalDual e) :
    scalarNormalPart e φ=φ := by
  let m := functionalModel φ
  change coefficient m.representation m.leftVector (normalProjection e m.representation m.rightVector)=φ
  rw [normalProjection_fixes_normal e _ _ _ (m.realizes.symm ▸ hφ),m.realizes]

end HochschildNormalPart

namespace HochschildNormalPart
universe u
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

omit [CompleteSpace X] in
lemma predual_separates {a b : M}
    (h : ∀ z,predualEmbedding e z a=predualEmbedding e z b) : a=b := by
  apply e.symm.injective
  ext z
  exact star_injective (h z)
end HochschildNormalPart
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Classical

namespace BoundedHochschild.KadisonRingrose

open HochschildNormalPart

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma universalGNS_positive_coefficient (ψ : M →ₚ[ℂ] ℂ) :
    ∀ a : M, coefficient universalGNSRepresentation
      (lp.single 2 ψ (positiveVector ψ)) (lp.single 2 ψ (positiveVector ψ)) a = ψ a := by
  classical
  intro a
  rw [coefficient_apply, lp.inner_single_left, universalGNSRepresentation_apply,
    lp.single_apply_self]
  exact positiveVector_coefficient ψ a

theorem normalGNSRepresentation_injective (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Function.Injective (normalGNSRepresentation e) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hzero (ξ : NormalGNS e) : universalGNSRepresentation a ξ = 0 := by
    have h := congrArg (fun A : NormalGNS e →L[ℂ] NormalGNS e =>
      (A ξ : UniversalGNS M)) ha
    exact h
  have hcoef (η : UniversalGNS M) :
      scalarNormalPart e (coefficient universalGNSRepresentation η η) a = 0 := by
    rw [scalarNormalPart_coefficient, coefficient_apply]
    have hp : normalProjection e universalGNSRepresentation η ∈ normalVectors e universalGNSRepresentation :=
      (normalVectors e universalGNSRepresentation).starProjection_apply_mem η
    rw [hzero ⟨_, hp⟩, inner_zero_right]
  have hnormal (φ : StrongDual ℂ M) (hφ : φ ∈ normalDual e) : φ a = 0 := by
    obtain ⟨ψ, _, hψ⟩ := HochschildPositiveDecomposition.exists_four_positive φ
    let f (i : Fin 4) : StrongDual ℂ M := coefficient universalGNSRepresentation
      (lp.single 2 (ψ i) (positiveVector (ψ i)))
      (lp.single 2 (ψ i) (positiveVector (ψ i)))
    have hf (i : Fin 4) (b : M) : f i b = ψ i b :=
      universalGNS_positive_coefficient (ψ i) b
    have heq : φ = f 0 - f 1 + Complex.I • (f 2 - f 3) := by
      ext b
      simpa only [add_apply, sub_apply, smul_apply, smul_eq_mul, hf] using hψ b
    have hfzero (i : Fin 4) : scalarNormalPart e (f i) a = 0 := hcoef _
    rw [← scalarNormalPart_fixes e hφ, heq, map_add, map_sub, map_smul, map_sub]
    simp only [add_apply, sub_apply, smul_apply, hfzero, smul_zero, sub_self, add_zero]
  apply predual_separates e
  intro z
  simpa only [map_zero] using hnormal (predualEmbedding e z) ⟨z, rfl⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normalGNS_nontrivial [Nontrivial M] (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Nontrivial (NormalGNS e) := by
  by_contra h
  let : Subsingleton (NormalGNS e) := not_nontrivial_iff_subsingleton.mp h
  exact one_ne_zero ((normalGNSRepresentation_injective e) (Subsingleton.elim
    (normalGNSRepresentation e 1) (normalGNSRepresentation e 0)))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u} : type_of% @OAI.BoundedHochschild.KadisonRingrose.normalGNS_nontrivial.{u} := @OAI.BoundedHochschild.KadisonRingrose.normalGNS_nontrivial.{u}
