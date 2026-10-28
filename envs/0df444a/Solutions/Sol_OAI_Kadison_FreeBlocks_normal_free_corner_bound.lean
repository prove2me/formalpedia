-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.normal_free_corner_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:05:09.873056+00:00
-- url     : https://prove2.me/submissions/497d5215-4b05-4f6b-81bd-c6c7b4ca571d

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C066
import Theorems.Thm_OAI_Kadison_CornerSymmetrization_bound_small_projection
import Theorems.Thm_OAI_Kadison_FreeBlocks_free_stage_symmetrization
import Theorems.Thm_OAI_Kadison_FreeBlocks_gns_vectorState
import Theorems.Thm_OAI_Kadison_FreeBlocks_stage_hankel_bound
import Theorems.Thm_OAI_Kadison_MatrixColumnCorner_exists_small_stage
import Theorems.Thm_OAI_Kadison_MatrixColumnCorner_full_column
import Theorems.Thm_OAI_Kadison_MatrixColumnCorner_minimal_projection
import Theorems.Thm_OAI_Kadison_MatrixColumnCorner_trace_minimal
import Theorems.Thm_OAI_Kadison_isStarProjection_corner
import Theorems.Thm_OAI_Kadison_projectionSymmetry_half
import Theorems.Thm_OAI_Kadison_projectionSymmetry_left
import Theorems.Thm_OAI_Kadison_projectionSymmetry_right
import Theorems.Thm_OAI_Kadison_unitary_dihedral

section
-- module Solutions.OAIQ039_CM.Commutator_NormalFreeCorner
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (D : VonNeumannAlgebra H)
  (t : FaithfulState A) (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))
  (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (S : Bool → StarSubalgebra ℂ A) (hS : S false=f.range)
  (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
  (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (inc : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (hinc : ∀ n m (h : n ≤ m) a, φ m (inc h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

include hS htr hinc hsize hDgen hgen in
theorem normal_free_corner_bound_oai
    (hnormal : NormalGNS.BoundedWOTContinuous D (factorTrace t f hf))
    (hdiffuse : DiffuseProjection.HasNoMinimalProjections D)
    (G : t.functional.GNS →L[ℂ] t.functional.GNS)
    (hGD : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)
    (s : unitary A) (hs : (s:A)∈S true) (hs0 : t.functional (s:A)=0)
    (hs2 : (s:A)*(s:A)=1)
    (ε β : ℝ) (hε : 0 ≤ ε) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hC : ∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) (β:ℂ) x → ‖G*x-x*G‖ ≤ ε*‖x‖) :
    ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0) (F:=t.functional.GNS)
      (baseEmbedding t S hfree).toContinuousLinearMap).comp
      ((G*t.functional.gnsStarAlgHom (s:A)-t.functional.gnsStarAlgHom (s:A)*G).comp
        (baseEmbedding t S hfree).toContinuousLinearMap)‖ ≤ 1040*ε := by
  classical
  let τ := factorTrace t f hf
  have hτ : ∀ a b : D, τ (a*b)=τ (b*a) := factorTrace_tracial t f hf htr
  have hone : τ 1=1 := (pullbackState t f hf).normalized
  have hfaith : ∀ a : D, τ (star a*a)=0 → a=0 := (pullbackState t f hf).faithful
  obtain ⟨V,_,hVW,hVD,hVC,hVe⟩ := free_stage_symmetrization t htr S f hS hfree hgen
    I φ inc hinc G ε hε β (s:A) hs hGD hC
  have hsmall (q : D) (hq : IsStarProjection q) (hqt : (τ q).re ≤ β)
      (x : t.functional.GNS →L[ℂ] t.functional.GNS) (hx : x∈ambientOperators t S)
      (hl : t.functional.gnsStarAlgHom (f q)*x=x)
      (hr : x*t.functional.gnsStarAlgHom (f q)=x) : ‖V*x-x*V‖ ≤ ε*‖x‖ :=
    CornerSymmetrization.bound_small_projection D τ hτ hnormal hfaith hone hdiffuse
      (t.functional.gnsStarAlgHom.comp f) (ambientOperators t S) (TracialGNS.vacuum t.functional)
      (fun a => gns_vectorState t.functional (f a)) V ε β hβ1 hVC q hq hqt x hx hl hr
  obtain ⟨n,hn⟩ := MatrixColumnCorner.exists_small_stage I hsize hβ
  let i0 : I n := Classical.choice inferInstance
  let q : Matrix (I n) (I n) ℂ := Matrix.single i0 i0 1
  have hq : IsStarProjection q := MatrixColumnCorner.minimal_projection i0
  have hqτ : τ (φ n q)=(Fintype.card (I n):ℂ)⁻¹ :=
    MatrixColumnCorner.trace_minimal τ hτ hone (φ n) i0
  have hqreal : (τ (φ n q)).re=(Fintype.card (I n):ℝ)⁻¹ := by
    rw [hqτ,←Complex.ofReal_natCast,←Complex.ofReal_inv,Complex.ofReal_re]
  have hqsmall := hsmall (φ n q) (hq.map (φ n)) (by rw [hqreal]; exact hn)
  obtain ⟨p0,hp0,_,hp0τ⟩ := NormalGNS.exists_prescribed_projection_trace D τ hτ hnormal
    hfaith hdiffuse 1 (IsStarProjection.one D) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ) ≤ (τ 1).re by rw [hone]; norm_num)
  have hp := hp0.map f
  let d0 := projectionSymmetry hp0
  let d : unitary A := ⟨f (d0:D),by
    constructor
    · rw [←map_star,←map_mul,d0.property.1,map_one]
    · rw [←map_star,←map_mul,d0.property.2,map_one]⟩
  have hdval : (d:A)=f (p0+p0-1) := rfl
  have hd2 : (d:A)*(d:A)=1 := by rw [hdval,←map_mul,projection_symmetry_square hp0,map_one]
  have hd : (d:A)∈S false := by rw [hS]; exact ⟨d0,rfl⟩
  have hpD : f p0∈S false := by rw [hS]; exact ⟨p0,rfl⟩
  have hτp : τ p0=(1/2:ℂ) := by
    apply Complex.ext
    · simpa using hp0τ
    · simpa using (τ.map_nonneg hp0.nonneg).2.symm
  have hd0 : t.functional (d:A)=0 := by
    change τ (p0+p0-1)=0
    rw [map_sub,map_add,hτp,hone]
    norm_num
  have hpform : f p0=(1/2:ℂ) • (1+(d:A)) := by
    have hh := congrArg f (projectionSymmetry_half hp0)
    simpa only [map_smul,map_add,map_one] using hh
  have hpd : f p0*(d:A)=f p0 := by
    change f p0*f (d0:D)=f p0
    rw [←map_mul,projectionSymmetry_left]
  have hdp : (d:A)*f p0=f p0 := by
    change f (d0:D)*f p0=f p0
    rw [←map_mul,projectionSymmetry_right]
  let γ : ℝ := min (β/2) (1/4)
  have hγ : 0<γ := lt_min (by positivity) (by norm_num)
  have hγβ : γ ≤ β := (min_le_left _ _).trans (by linarith)
  have hγp : γ ≤ (τ p0).re := by rw [hp0τ]; exact (min_le_right _ _).trans (by norm_num)
  obtain ⟨e0,he0,he0p,he0τ⟩ := NormalGNS.exists_prescribed_projection_trace D τ hτ hnormal
    hfaith hdiffuse p0 hp0 hγ.le hγp
  let e : Corner hp := ⟨f e0,by
    constructor
    · rw [←map_mul,(he0.le_iff_mul_eq_right hp0).mp he0p]
    · rw [←map_mul,(he0.le_iff_mul_eq_left hp0).mp he0p]⟩
  have heproj : IsStarProjection e := isStarProjection_corner hp (he0.map f)
  have he : e∈cornerFactor hp (S false) hpD := by
    change f e0∈S false
    rw [hS]; exact ⟨e0,rfl⟩
  have hr : 0<‖TracialGNS.algebraVector τ e0‖ := by
    apply norm_pos_iff.mpr
    intro hz
    have hzτ : τ e0=0 := by
      rw [←he0.isIdempotentElem.eq,←he0.isSelfAdjoint.star_eq,
        ←TracialGNS.inner_algebraVector,hz,inner_zero_left]
    have hzr := congrArg Complex.re hzτ
    rw [he0τ,Complex.zero_re] at hzr
    exact (ne_of_gt hγ) hzr
  have heqt : (τ e0).re ≤ β := by rw [he0τ]; exact hγβ
  have hsmalle (a : A) (ha : (e:A)*a*(e:A)=a) :
      ‖V*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*V‖ ≤ ε*‖a‖ := by
    have hl : f e0*a=a := by
      change f e0*a*f e0=a at ha
      calc
        _=f e0*(f e0*a*f e0) := by rw [ha]
        _=f e0*a*f e0 := by rw [←mul_assoc,←mul_assoc,←map_mul,he0.isIdempotentElem.eq]
        _=a := ha
    have hr' : a*f e0=a := by
      change f e0*a*f e0=a at ha
      calc
        _=(f e0*a*f e0)*f e0 := by rw [ha]
        _=f e0*a*f e0 := by rw [mul_assoc,←map_mul,he0.isIdempotentElem.eq]
        _=a := ha
    exact (hsmall e0 he0 heqt (t.functional.gnsStarAlgHom a)
      ((mem_ambientOperators t S).mpr (hgen a))
      (by rw [←map_mul,hl]) (by rw [←map_mul,hr'])).trans
        (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le t.functional.gnsStarAlgHom a) hε)
  have hα : (0:ℝ)<(Fintype.card (I n):ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  obtain ⟨hcol,hinit,htotal⟩ := MatrixColumnCorner.full_column (φ n) i0
  have hbound := stage_hankel_bound t htr S f hf hS hfree I φ inc hinc hsize hDgen hgen
    V hVD hVW (ambientVonNeumann t S) (fun a => (mem_ambientOperators t S).mpr (hgen a))
    d s hd hs hd0 hs0 (unitary_dihedral hd2 hs2) hd2 hs2 hp hpform hpd hdp hpD
    n q hq (Fintype.card (I n):ℝ)⁻¹ hα
    (by change τ (φ n q)=_; rw [hqτ,Complex.ofReal_inv,Complex.ofReal_natCast])
    (fun i => φ n (Matrix.single i i0 1)) hcol hinit htotal e0 e rfl heproj he hr
    ε hε hqsmall hsmalle
  rw [hVe] at hbound
  exact hbound

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.FreeBlocks.normal_free_corner_bound_oai.{u_1} := @OAI.Kadison.FreeBlocks.normal_free_corner_bound_oai.{u_1}
