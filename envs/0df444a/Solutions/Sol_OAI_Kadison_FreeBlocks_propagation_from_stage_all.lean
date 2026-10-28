-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.propagation_from_stage_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:33:43.443354+00:00
-- url     : https://prove2.me/submissions/7cf12df9-8152-479e-9700-cb123f85c648

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_FreeBlocks_propagation_from_corner
import Theorems.Thm_OAI_Kadison_TracialGNS_exists_corner_weak_zero

section
-- module Solutions.OAIQ039_CM.Commutator_FreePropagationEstimate
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open Filter _root_.Topology ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

lemma norm_factorVector (d : D) :
    ‖TracialGNS.algebraVector (factorTrace t f hf) d‖=
      ‖(t.functional.toPreGNS (f d) : t.functional.GNS)‖ := by
  simp only [TracialGNS.algebraVector_apply,UniformSpace.Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.ofPreGNS_toPreGNS,
    pullbackState_apply,map_mul,map_star]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreePropagationStage
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open Filter Topology ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
  (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)
  (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
  (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)
  (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
  (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer
      (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

variable (hGL : ∀ d : D, G.comp (t.functional.gnsStarAlgHom (f d))=
  (t.functional.gnsStarAlgHom (f d)).comp G)

variable (M : VonNeumannAlgebra t.functional.GNS)
  (hM : ∀ a : A, t.functional.gnsStarAlgHom a∈M)

include htr he hsize hDgen hgen hB hGL hM in
theorem propagation_from_stage {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : letterSpace t S j) (hs : ‖s‖=1)
    (n : ℕ) (p : Matrix (I n) (I n) ℂ) (hp : IsStarProjection p)
    (α : ℝ) (hα : 0<α) (hατ : factorTrace t f hf (φ n p)=(α:ℂ))
    (w : κ → D)
    (hcol : ∀ i j, star (w i)*w j=if i=j then φ n p else 0)
    (hinit : ∀ i, φ n p*star (w i)=star (w i))
    (htotal : ∑ i, w i*star (w i)=1)
    (ε : ℝ) (hε : 0≤ε)
    (hsmall : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
      t.functional.gnsStarAlgHom (f (φ n p))*a=a →
      a*t.functional.gnsStarAlgHom (f (φ n p))=a → ‖G.comp a-a.comp G‖≤ε*‖a‖)
    (k : ℕ) (v : multiplicityLevel t S j 0) :
    ‖B (k+1) (repeatInsertion t S s hs (k+1) v)-
      repeatInsertion t S s hs (k+1) (B 0 v)‖≤32*ε*‖v‖ := by
  have h1 : factorTrace t f hf 1=1 := by
    change t.functional (f 1)=1
    simpa only [map_one] using t.normalized
  obtain ⟨y,hy,hm⟩ := TracialGNS.exists_corner_weak_zero (factorTrace t f hf)
    (factorTrace_tracial t f hf htr) h1 I φ e he hsize hDgen n p hp α hα hατ
  have hy0 (l : ℕ) : t.functional (f (y l))=0 := (hy l).1
  have hym (l : ℕ) : f (y l)∈S i := by rw [hS]; exact ⟨y l,rfl⟩
  let x : ℕ → letterSpace t S i := fun l => letterOf t S i (f (y l)) (hym l) (hy0 l)
  have hxv (l : ℕ) : letterValue t S i (x l)=f (y l) := letterValue_letterOf _ _ _ _ _ _
  have hnorm (a : D) : ‖t.functional.toPreGNS (f a)‖=‖(factorTrace t f hf).toPreGNS a‖ := by
    have ht := norm_factorVector t f hf a
    simpa only [TracialGNS.algebraVector_apply,UniformSpace.Completion.norm_coe] using ht.symm
  have hxn (l : ℕ) : ‖x l‖=1 := by
    change ‖t.functional.toPreGNS (f (y l))‖=1
    rw [hnorm]
    exact (hy l).2.2.2.2.1
  have hxq (l : ℕ) : letterValue t S i (x l)*f (φ n p)=letterValue t S i (x l) := by
    rw [hxv,←map_mul,(hy l).2.1]
  have hxx (l : ℕ) : star (letterValue t S i (x l))*letterValue t S i (x l)=
      ((α⁻¹:ℝ):ℂ) • f (φ n p) := by
    rw [hxv,←map_star,←map_mul,(hy l).2.2.1,map_smul,Complex.ofReal_inv]
  have hxs (l : ℕ) : ‖t.functional.toPreGNS (star (letterValue t S i (x l)))‖≤1 := by
    rw [hxv,←map_star,hnorm,(hy l).2.2.2.2.2]
  have hxmoment : ∀ a ∈ S i,
      Tendsto (fun l => t.functional (letterValue t S i (x l)*a)) atTop (𝓝 0) := by
    intro a ha
    rw [hS] at ha
    obtain ⟨b,rfl⟩ := ha
    have hb := hm b
    change Tendsto (fun l => t.functional (f (y l*b))) atTop (𝓝 0) at hb
    change Tendsto (fun l => t.functional (letterValue t S i (x l)*f b)) atTop (𝓝 0)
    simpa only [hxv,map_mul] using hb
  have hxb (l : ℕ) : ‖letterValue t S i (x l)‖≤(Real.sqrt α)⁻¹ := by
    rw [hxv]
    exact (NonUnitalStarAlgHom.norm_apply_le f _).trans (hy l).2.2.2.1
  let : Nontrivial A := ⟨⟨1,0,by
    intro h
    have hh := t.normalized
    rw [h,map_zero] at hh
    exact zero_ne_one hh⟩⟩
  let R := (‖letterValue t S j s‖*(Real.sqrt α)⁻¹)^k*‖letterValue t S j s‖
  have hR (l : ℕ) : ‖(letterValue t S j s*letterValue t S i (x l))^k*letterValue t S j s‖≤R := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_pow_le _ _).trans
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (hxb l) (norm_nonneg _))) k
  exact propagation_from_corner t S f hf hS hfree hij G B hB hGL M hM s hs
    (φ n p) (hp.map (φ n)) w hcol hinit htotal α⁻¹ (by positivity) x hxn hxq hxx hxs
    hxmoment hgen k R hR ε hε hsmall v

lemma repeatInsertion_zero (s : letterSpace t S j) (hs : ‖s‖=1)
    (v : multiplicityLevel t S j 0) : repeatInsertion t S s hs 0 v=v := by
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v => rw [repeatInsertion_coe]; rfl

include htr he hsize hDgen hgen hB hGL hM in
theorem propagation_from_stage_all_oai {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : letterSpace t S j) (hs : ‖s‖=1)
    (n : ℕ) (p : Matrix (I n) (I n) ℂ) (hp : IsStarProjection p)
    (α : ℝ) (hα : 0<α) (hατ : factorTrace t f hf (φ n p)=(α:ℂ))
    (w : κ → D)
    (hcol : ∀ i j, star (w i)*w j=if i=j then φ n p else 0)
    (hinit : ∀ i, φ n p*star (w i)=star (w i))
    (htotal : ∑ i, w i*star (w i)=1)
    (ε : ℝ) (hε : 0≤ε)
    (hsmall : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
      t.functional.gnsStarAlgHom (f (φ n p))*a=a →
      a*t.functional.gnsStarAlgHom (f (φ n p))=a → ‖G.comp a-a.comp G‖≤ε*‖a‖)
    (k : ℕ) (v : multiplicityLevel t S j 0) :
    ‖B k (repeatInsertion t S s hs k v)-
      repeatInsertion t S s hs k (B 0 v)‖≤32*ε*‖v‖ := by
  cases k with
  | zero =>
      rw [repeatInsertion_zero t S s hs v,repeatInsertion_zero t S s hs (B 0 v),sub_self]
      change ‖(0 : UniformSpace.Completion (factorSpace t S j))‖≤32*ε*‖v‖
      calc
        ‖(0 : UniformSpace.Completion (factorSpace t S j))‖ = 0 := _root_.norm_zero
        _ ≤ 32*ε*‖v‖ := by positivity
  | succ k =>
      exact propagation_from_stage t htr S f hf hS hfree hij I φ e he
        hsize hDgen hgen G B hB hGL M hM s hs n p hp α hα hατ w hcol hinit htotal
        ε hε hsmall k v

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.FreeBlocks.propagation_from_stage_all_oai.{u_1, u_2, u_3} := @OAI.Kadison.FreeBlocks.propagation_from_stage_all_oai.{u_1, u_2, u_3}
