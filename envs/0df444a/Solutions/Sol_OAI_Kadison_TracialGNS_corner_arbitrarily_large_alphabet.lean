-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:19:30.925979+00:00
-- url     : https://prove2.me/submissions/07d43131-61b1-4838-98e1-74a156603017

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C013
import Theorems.Thm_OAI_Kadison_MatrixCorners_normalizedStageAlphabet_centered
import Theorems.Thm_OAI_Kadison_MatrixCorners_normalizedStageAlphabet_orthonormal
import Theorems.Thm_OAI_Kadison_MatrixCorners_projection_rank

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixProjectionDiagonal
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] Classical.propDecidable

lemma projection_eigenvalue (p : Matrix I I ℂ) (hp : IsStarProjection p) (i : I) :
    (projection_hermitian p hp).eigenvalues i=0 ∨ (projection_hermitian p hp).eigenvalues i=1 := by
  let U := (projection_hermitian p hp).eigenvectorUnitary
  have hid := congrArg (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star U)) hp.isIdempotentElem.eq
  rw [map_mul] at hid
  have hd := (projection_hermitian p hp).conjStarAlgAut_star_eigenvectorUnitary
  change Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (star U) p = _ at hd
  rw [hd] at hid
  have h := congrArg (fun M : Matrix I I ℂ => (M i i).re) hid
  simp only [Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply_eq,Function.comp_apply,
    ] at h
  change ((projection_hermitian p hp).eigenvalues i : ℂ).re *
    ((projection_hermitian p hp).eigenvalues i : ℂ).re -
    ((projection_hermitian p hp).eigenvalues i : ℂ).im *
    ((projection_hermitian p hp).eigenvalues i : ℂ).im =
    ((projection_hermitian p hp).eigenvalues i : ℂ).re at h
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at h
  have hz : (projection_hermitian p hp).eigenvalues i *
      ((projection_hermitian p hp).eigenvalues i-1)=0 := by nlinarith
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp

lemma projection_diagonal_form (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    p=Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) (projection_hermitian p hp).eigenvectorUnitary
      (Matrix.diagonal (fun i => if i∈projectionIndices p hp then (1:ℂ) else 0)) := by
  apply (projection_hermitian p hp).spectral_theorem.trans
  congr 1
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Function.comp_apply,projectionIndices,Set.mem_ofPred_eq]
    rcases projection_eigenvalue p hp i with he|he <;> simp [he]
  · simp [Matrix.diagonal_apply_ne _ h]

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCutEmbedding
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

attribute [local instance] Classical.propDecidable

lemma cutEmbedding_one (s : Set I) :
    cutEmbedding s 1=Matrix.diagonal (fun i => if i∈s then (1:ℂ) else 0) := by
  ext i j
  by_cases hi : i∈s <;> by_cases hj : j∈s
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi,Equiv.Set.sumCompl_symm_apply_of_mem hj]
    simp [Matrix.one_apply,Matrix.diagonal_apply,hi]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_mem hi,Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    simp [show i≠j from fun h=>hj (h ▸ hi)]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi,Equiv.Set.sumCompl_symm_apply_of_mem hj]
    simp [Matrix.diagonal_apply,hi]
  · change Matrix.fromBlocks (1:Matrix s s ℂ) 0 0 0
      ((Equiv.Set.sumCompl s).symm i) ((Equiv.Set.sumCompl s).symm j)=_
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hi,Equiv.Set.sumCompl_symm_apply_of_notMem hj]
    simp [Matrix.diagonal_apply,hi]

lemma projectionEmbedding_one (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    projectionEmbedding p hp 1=p := by
  change Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) _ (cutEmbedding _ 1)=p
  rw [cutEmbedding_one]
  exact (projection_diagonal_form p hp).symm

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixUnitaryAlphabet
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

lemma shift_star_mul (g h : G) : star (shiftMatrix g)*shiftMatrix h=shiftMatrix (h-g) := by
  change (shiftMatrix g).conjTranspose*shiftMatrix h=_
  simp only [shiftMatrix,Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul]
  congr 1
  ext x
  simp [sub_eq_add_neg]

omit [Fintype G] in
lemma shift_zero : shiftMatrix (0:G)=1 := by
  change (Equiv.addLeft (0:G)).permMatrix ℂ=1
  have he : Equiv.addLeft (0:G)=Equiv.refl G := by ext x; simp
  rw [he,Matrix.permMatrix_refl]

lemma projectionAlphabet_star_mul (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) :
    star (projectionAlphabet p hp e g)*projectionAlphabet p hp e g=p := by
  unfold projectionAlphabet
  rw [←map_star,←map_mul,←map_star,←map_mul,shift_star_mul,sub_self,shift_zero,
    map_one,projectionEmbedding_one]

lemma projectionAlphabet_support (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) : projectionAlphabet p hp e g*p=
      projectionAlphabet p hp e g := by
  change projectionEmbedding p hp _ * p=projectionEmbedding p hp _
  conv_lhs => rhs; rw [←projectionEmbedding_one p hp]
  rw [←map_mul,mul_one]

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerAlphabetGNS
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (p : Matrix I I ℂ) (hp : IsStarProjection p)
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  (e : G ≃ projectionIndices p hp)

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_star_mul (g : G) : star (stageAlphabet φ p hp e g)*stageAlphabet φ p hp e g=φ p := by
  rw [stageAlphabet,←map_star,←map_mul,projectionAlphabet_star_mul]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_support (g : G) : stageAlphabet φ p hp e g*φ p=stageAlphabet φ p hp e g := by
  rw [stageAlphabet,←map_mul,projectionAlphabet_support]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma stageAlphabet_norm_le (g : G) : ‖stageAlphabet φ p hp e g‖≤1 := by
  have h := CStarRing.norm_star_mul_self (x := stageAlphabet φ p hp e g)
  rw [stageAlphabet_star_mul] at h
  have hp1 := (hp.map φ).norm_le (φ p)
  nlinarith [norm_nonneg (stageAlphabet φ p hp e g)]

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

include hα in
lemma normalization_sq : ((((Real.sqrt α)⁻¹:ℝ):ℂ))^2=(α:ℂ)⁻¹ := by
  rw [←Complex.ofReal_pow,inv_pow,Real.sq_sqrt hα.le,Complex.ofReal_inv]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma normalizedStageAlphabet_norm_le (g : G) : ‖normalizedStageAlphabet φ p hp e α g‖≤(Real.sqrt α)⁻¹ := by
  rw [normalizedStageAlphabet,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg α))]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (stageAlphabet_norm_le φ p hp e g)
    (inv_nonneg.mpr (Real.sqrt_nonneg α))

include hα in
omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma normalizedStageAlphabet_star_mul (g : G) :
    star (normalizedStageAlphabet φ p hp e α g)*normalizedStageAlphabet φ p hp e α g=
      ((α:ℂ)⁻¹) • φ p := by
  rw [normalizedStageAlphabet,star_smul,smul_mul_smul_comm,Complex.star_def,Complex.conj_ofReal,
    stageAlphabet_star_mul,←sq,normalization_sq α hα]

omit [PartialOrder A] [StarOrderedRing A] [Nonempty I] in
lemma normalizedStageAlphabet_support (g : G) :
    normalizedStageAlphabet φ p hp e α g*φ p=normalizedStageAlphabet φ p hp e α g := by
  rw [normalizedStageAlphabet,smul_mul_assoc,stageAlphabet_support]

include hτ h1 hα hατ hp in
theorem exists_normalized_corner_alphabet (N : ℕ)
    (hN : (N+1:ℝ)≤α*Fintype.card I) :
    ∃ m : ℕ, N ≤ m ∧ ∃ x : Fin m → A,
      Orthonormal ℂ (fun i => TracialGNS.algebraVector τ (x i)) ∧
      ∀ i, τ (x i)=0 ∧ x i*φ p=x i ∧ star (x i)*x i=((α:ℂ)⁻¹) • φ p ∧
        ‖x i‖≤(Real.sqrt α)⁻¹ := by
  let r := Fintype.card (projectionIndices p hp)
  have hrN : N+1 ≤ r := by
    have h := hN.trans_eq (projection_rank τ hτ h1 φ p hp α hατ).symm
    exact_mod_cast h
  have hr : 0 < r := by omega
  let : NeZero r := ⟨hr.ne'⟩
  let e : ZMod r ≃ projectionIndices p hp := Fintype.equivOfCardEq (by rw [ZMod.card])
  let J := {g : ZMod r // g≠0}
  let m := Fintype.card J
  have hm : m=r-1 := by
    dsimp only [m,J]
    rw [Fintype.card_subtype_compl (fun g : ZMod r => g=0),Fintype.card_subtype_eq,ZMod.card]
  let b : Fin m ≃ J := (Fintype.equivFin J).symm
  let x : Fin m → A := fun i => normalizedStageAlphabet φ p hp e α (b i).val
  refine ⟨m,by omega,x,?_,?_⟩
  · exact (normalizedStageAlphabet_orthonormal τ hτ h1 φ p hp e α hα hατ).comp
      (fun i => (b i).val) (Subtype.val_injective.comp b.injective)
  · intro i
    exact ⟨normalizedStageAlphabet_centered τ hτ h1 φ p hp e α _ (b i).property,
      normalizedStageAlphabet_support φ p hp e α _,
      normalizedStageAlphabet_star_mul φ p hp e α hα _,
      normalizedStageAlphabet_norm_le φ p hp e α _⟩

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerWeakZero
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

open Filter Topology

open scoped Matrix.Norms.L2Operator

namespace Kadison.TracialGNS

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ)
  (hτ : ∀ a b, τ (a*b)=τ (b*a))
  (h1 : τ 1=1)
  (I : ℕ → Type*)
  [∀ n, Fintype (I n)]
  [∀ n, DecidableEq (I n)]
  [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
  (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

include hτ h1 e he hsize in
lemma corner_arbitrarily_large_alphabet_oai (n : ℕ) (p : Matrix (I n) (I n) ℂ)
    (hp : IsStarProjection p) (α : ℝ) (hα : 0<α) (hατ : τ (φ n p)=(α:ℂ)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ x : Fin m → A,
      Orthonormal ℂ (fun i => algebraVector τ (x i)) ∧
      ∀ i, τ (x i)=0 ∧ x i*φ n p=x i ∧ star (x i)*x i=((α:ℂ)⁻¹) • φ n p ∧
        ‖x i‖≤(Real.sqrt α)⁻¹ := by
  obtain ⟨q,hq⟩ := exists_nat_ge ((N+1:ℝ)/α)
  obtain ⟨k,hk,hqk⟩ := hsize n q
  have hN : (N+1:ℝ)≤α*Fintype.card (I k) := by
    rw [mul_comm]
    exact (div_le_iff₀ hα).mp (hq.trans (by exact_mod_cast hqk))
  have htrace : τ (φ k (e hk p))=(α:ℂ) := by rw [he]; exact hατ
  obtain ⟨m,hm,x,hx,hprop⟩ := MatrixCorners.exists_normalized_corner_alphabet τ hτ h1
    (φ k) (e hk p) (hp.map (e hk)) α hα htrace N hN
  exact ⟨m,hm,x,hx,by simpa only [he] using hprop⟩

end Kadison.TracialGNS

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet_oai.{u_1, u_2} := @OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet_oai.{u_1, u_2}
