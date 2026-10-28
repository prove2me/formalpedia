-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.exists_free_symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:59:10.139678+00:00
-- url     : https://prove2.me/submissions/ed9671ec-13bb-413a-8dc1-ad0168d7099c

import Mathlib
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_CompactAverage_exists_stage_average
import Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_commutes_other
import Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_conj_mem_bicommutant
import Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_continuous
import Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_fixes_baseProjection

section
-- module Solutions.OAIQ039_CM.Commutator_CornerSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMap MeasureTheory MeasureTheory.Measure

namespace Kadison.CornerSymmetrization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma vectorState_conj (U : H ≃ₗᵢ[ℂ] H) (Ω : H) (hΩ : U Ω=Ω) (a : H →L[ℂ] H) :
    vectorState Ω (U.conjStarAlgEquiv a)=vectorState Ω a := by
  have hi : U.symm Ω=Ω := by
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply,hΩ]
  change inner ℂ Ω (U (a (U.symm Ω)))=inner ℂ Ω (a Ω)
  rw [hi]
  calc
    inner ℂ Ω (U (a Ω)) = inner ℂ (U Ω) (U (a Ω)) := by rw [hΩ]
    _ = inner ℂ Ω (a Ω) := U.inner_map_map Ω (a Ω)

lemma cornerElement_map (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
    (U : H ≃ₗᵢ[ℂ] H) (hΩ : U Ω=Ω)
    (hD : ∀ a∈D, U.conjStarAlgEquiv a∈D) (hP : ∀ a∈P, U.conjStarAlgEquiv a∈P)
    {x : H →L[ℂ] H} (hx : CornerElement D P Ω t x) :
    CornerElement D P Ω t (U.conjStarAlgEquiv x) := by
  obtain ⟨hx,e,he,hp,ht,hel,her⟩ := hx
  refine ⟨hP x hx,U.conjStarAlgEquiv e,hD e he,?_,?_,?_,?_⟩
  · exact hp.map U.conjStarAlgEquiv
  · rw [vectorState_conj U Ω hΩ,ht]
  · simpa only [map_mul] using congrArg U.conjStarAlgEquiv hel
  · simpa only [map_mul] using congrArg U.conjStarAlgEquiv her

lemma commutator_conj_norm (α : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H))
    (G a : H →L[ℂ] H) :
    ‖α G*a-a*α G‖=‖G*α.symm a-α.symm a*G‖ := by
  calc
    _ = ‖α (G*α.symm a-α.symm a*G)‖ := by
      simp only [map_sub,map_mul,StarAlgEquiv.apply_symm_apply]
    _ = _ := StarAlgEquiv.norm_map α _

lemma commutator_adjoint_norm (G a : H →L[ℂ] H) :
    ‖G.adjoint*a-a*G.adjoint‖=‖G*star a-star a*G‖ := by
  have h : G.adjoint*a-a*G.adjoint = -star (G*star a-star a*G) := by
    simp only [star_sub,star_mul,star_star,neg_sub]
    rfl
  rw [h,norm_neg,norm_star]

lemma cornerElement_star (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
    {x : H →L[ℂ] H} (hx : CornerElement D P Ω t x) :
    CornerElement D P Ω t (star x) := by
  obtain ⟨hx,e,he,hp,ht,hel,her⟩ := hx
  refine ⟨star_mem hx,e,he,hp,ht,?_,?_⟩
  · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star her
  · simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hel

lemma fixed_projection_right (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H)
    (hQ : IsSelfAdjoint Q) (hU : (U:H →L[ℂ] H)*Q=Q) :
    Q*(U:H →L[ℂ] H)=Q := by
  have h := congrArg star hU
  simp only [star_mul,hQ.star_eq] at h
  have hu : star (U:H →L[ℂ] H)*(U:H →L[ℂ] H)=1 := by
    rw [LinearIsometryEquiv.star_eq_symm]
    ext x
    change U.symm (U x)=x
    exact U.symm_apply_apply x
  have h' := congrArg (fun a : H →L[ℂ] H => a*(U:H →L[ℂ] H)) h
  rw [mul_assoc,hu,mul_one] at h'
  exact h'.symm

lemma fixed_compressed_conjugate (U : H ≃ₗᵢ[ℂ] H) (Q s G : H →L[ℂ] H)
    (hQ : IsSelfAdjoint Q) (hU : (U:H →L[ℂ] H)*Q=Q)
    (hs : (U:H →L[ℂ] H)*s=s*(U:H →L[ℂ] H)) :
    Q*(U.conjStarAlgEquiv G*s-s*U.conjStarAlgEquiv G)*Q=Q*(G*s-s*G)*Q := by
  let u : H →L[ℂ] H := U
  let v : H →L[ℂ] H := U.symm
  have huv : u*v=1 := by ext x; exact U.apply_symm_apply x
  have hvu : v*u=1 := by ext x; exact U.symm_apply_apply x
  have hQu : Q*u=Q := fixed_projection_right U Q hQ hU
  have hvQ : v*Q=Q := by
    have h := congrArg (fun a => v*a) hU
    change v*(u*Q)=v*Q at h
    rw [←mul_assoc,hvu,one_mul] at h
    exact h.symm
  have hvs : v*s=s*v := by
    have h := congrArg (fun a => v*a*v) hs
    change v*(u*s)*v=v*(s*u)*v at h
    have hss : v*(u*s)*v=s*v := by rw [←mul_assoc v u s,hvu,one_mul]
    have htt : v*(s*u)*v=v*s := by
      calc
        _ = (v*s)*(u*v) := by noncomm_ring
        _ = v*s := by rw [huv,mul_one]
    rw [hss,htt] at h
    exact h.symm
  change Q*(u*G*v*s-s*(u*G*v))*Q=Q*(G*s-s*G)*Q
  simp only [mul_sub,sub_mul]
  congr 1
  · calc
      Q*(u*G*v*s)*Q = Q*u*G*(v*s)*Q := by noncomm_ring
      _ = Q*G*(s*v)*Q := by rw [hQu,hvs]
      _ = Q*G*s*(v*Q) := by noncomm_ring
      _ = Q*(G*s)*Q := by rw [hvQ]; noncomm_ring
  · calc
      Q*(s*(u*G*v))*Q=Q*(s*u)*G*(v*Q) := by noncomm_ring
      _ = Q*(u*s)*G*Q := by rw [←hs,hvQ]
      _ = Q*(s*G)*Q := by rw [←mul_assoc,hQu]; noncomm_ring

lemma conj_symm (U : H ≃ₗᵢ[ℂ] H) : U.symm.conjStarAlgEquiv=U.conjStarAlgEquiv.symm := by
  apply StarAlgEquiv.ext
  intro a
  apply U.conjStarAlgEquiv.injective
  change U.conjStarAlgEquiv (U.symm.conjStarAlgEquiv a)=U.conjStarAlgEquiv (U.conjStarAlgEquiv.symm a)
  rw [StarAlgEquiv.apply_symm_apply]
  ext x
  change U (U.symm (a (U (U.symm x))))=a x
  simp only [LinearIsometryEquiv.apply_symm_apply]

variable (Γ : ℕ → Type*) [∀ n, Group (Γ n)] [∀ n, TopologicalSpace (Γ n)]
  [∀ n, IsTopologicalGroup (Γ n)] [∀ n, CompactSpace (Γ n)]
  [∀ n, MeasurableSpace (Γ n)] [∀ n, BorelSpace (Γ n)]

variable (U : ∀ n, Γ n →* (H ≃ₗᵢ[ℂ] H))
  (hU : ∀ n x, Continuous fun g => U n g x)
  (hnest : ∀ i j, i≤j → ∀ g : Γ i, ∃ k : Γ j, U j k=U i g)

variable (μ : ∀ n, Measure (Γ n)) [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsMulLeftInvariant (μ n)]

variable (D P : StarSubalgebra ℂ (H →L[ℂ] H)) (Ω : H) (t : ℂ)
  (hΩ : ∀ n g, U n g Ω=Ω)
  (hD : ∀ n g a, a∈D → (U n g).conjStarAlgEquiv a∈D)
  (hP : ∀ n g a, a∈P → (U n g).conjStarAlgEquiv a∈P)

variable (G : H →L[ℂ] H) (ε : ℝ) (hε : 0≤ε)
  (hGD : ∀ a∈D, G*a=a*G)
  (hC : ∀ x, CornerElement D P Ω t x → ‖G*x-x*G‖≤ε*‖x‖)

variable (Q s : H →L[ℂ] H) (hQ : IsSelfAdjoint Q)
  (hUQ : ∀ n g, (U n g:H →L[ℂ] H)*Q=Q)
  (hUs : ∀ n g, (U n g:H →L[ℂ] H)*s=s*(U n g:H →L[ℂ] H))

include hU hnest μ hΩ hD hP hε hGD hC hQ hUQ hUs in
theorem exists_symmetrization : ∃ V : H →L[ℂ] H,
    ‖V‖≤‖G‖ ∧ (∀ n g, V*(U n g:H →L[ℂ] H)=(U n g:H →L[ℂ] H)*V) ∧
    (∀ a∈D, V*a=a*V) ∧
    (∀ x, CornerElement D P Ω t x → ‖V*x-x*V‖≤ε*‖x‖) ∧
    (∀ x, CornerElement D P Ω t x → ‖V.adjoint*x-x*V.adjoint‖≤ε*‖x‖) ∧
    Q*(V*s-s*V)*Q=Q*(G*s-s*G)*Q := by
  let ι := Sum {a : H →L[ℂ] H // a∈D} {x : H →L[ℂ] H // CornerElement D P Ω t x}
  let a : ι → H →L[ℂ] H := Sum.elim Subtype.val Subtype.val
  let C : ι → ℝ := Sum.elim (fun _ => 0) (fun x => ε*‖x.val‖)
  have hC₀ : ∀ i, 0≤C i := by
    intro i
    cases i with
    | inl x => exact le_rfl
    | inr x => exact mul_nonneg hε (norm_nonneg _)
  have hstar (n : ℕ) (g : Γ n) : (U n g).conjStarAlgEquiv.symm=(U n g⁻¹).conjStarAlgEquiv := by
    rw [map_inv,LinearIsometryEquiv.inv_def,conj_symm]
  have hb : ∀ n g i, ‖CompactAverage.conjugate (U n) G g*a i-a i*CompactAverage.conjugate (U n) G g‖≤C i := by
    intro n g i
    change ‖(U n g).conjStarAlgEquiv G*a i-a i*(U n g).conjStarAlgEquiv G‖≤C i
    rw [commutator_conj_norm,hstar]
    cases i with
    | inl x =>
      change ‖G*(U n g⁻¹).conjStarAlgEquiv x.val-(U n g⁻¹).conjStarAlgEquiv x.val*G‖≤0
      rw [hGD _ (hD n g⁻¹ x.val x.property),sub_self,norm_zero]
    | inr x =>
      change ‖G*(U n g⁻¹).conjStarAlgEquiv x.val-(U n g⁻¹).conjStarAlgEquiv x.val*G‖≤ε*‖x.val‖
      simpa only [StarAlgEquiv.norm_map] using hC _
        (cornerElement_map D P Ω t (U n g⁻¹) (hΩ n g⁻¹) (hD n g⁻¹) (hP n g⁻¹) x.property)
  obtain ⟨V,hV,hVU,hVC,hVQ⟩ := CompactAverage.exists_stage_average Γ U hU hnest μ G a C hC₀ hb Q Q s
    (fun n g => fixed_compressed_conjugate (U n g) Q s G hQ (hUQ n g) (hUs n g))
  have hVC' : ∀ x, CornerElement D P Ω t x → ‖V*x-x*V‖≤ε*‖x‖ := by
    intro x hx
    exact hVC (Sum.inr ⟨x,hx⟩)
  refine ⟨V,hV,hVU,?_,hVC',?_,hVQ⟩
  · intro x hx
    have h := hVC (Sum.inl ⟨x,hx⟩)
    change ‖V*x-x*V‖≤0 at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  · intro x hx
    rw [commutator_adjoint_norm]
    simpa only [norm_star] using hVC' (star x) (cornerElement_star D P Ω t hx)

end Kadison.CornerSymmetrization

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionCovariance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ i a, a∈S i → α i a∈S i)
  (hτ : ∀ i a, t.functional (α i a)=t.functional a)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_generator_word (i : ι) (a : A) (ha : a∈S i)
    (w : List (Letter S t.functional.toLinearMap)) (hw : Reduced w) :
    action t S α hmem hτ hfree hgen (TracialGNS.algebraVector t.functional (a*word w)) =
      TracialGNS.algebraVector t.functional
        (α i a*word (w.map (letter t S α hmem hτ))) := by
  let V := TracialGNS.algebraVector t.functional
  let W := action t S α hmem hτ hfree hgen
  have hword : ∀ w, Reduced w → W (V (word w))=V (word (w.map (letter t S α hmem hτ))) :=
    fun w hw => action_word t S α hmem hτ hfree hgen w hw
  have hone : W (V 1)=V 1 := hword [] reduced_nil
  let c : Letter S t.functional.toLinearMap :=
    ⟨i,a-t.functional a • (1:A),sub_mem ha (SMulMemClass.smul_mem _ (one_mem _)),
      by simp [map_sub,map_smul,t.normalized]⟩
  change W (V (a*word w))=V (α i a*word (w.map (letter t S α hmem hτ)))
  cases w with
  | nil =>
    have h := hword [c] (List.IsChain.singleton c)
    change W (V ((a-t.functional a • (1:A))*1)) =
      V (α i (a-t.functional a • (1:A))*1) at h
    simp only [mul_one,map_sub,map_smul,map_one,hone] at h
    simpa only [word_nil,List.map_nil,mul_one] using (sub_left_inj.mp h)
  | cons b w =>
    by_cases hib : i=b.color
    · let d : Letter S t.functional.toLinearMap :=
        ⟨i,a*b.val-t.functional (a*b.val) • (1:A),
          sub_mem (mul_mem ha (by simpa only [hib] using b.mem))
            (SMulMemClass.smul_mem _ (one_mem _)),
          by simp [map_sub,map_smul,t.normalized]⟩
      have hd : Reduced (d::w) := by
        exact hw.imp_head (by intro c hc; simpa only [d,hib] using hc)
      have ht := hword w hw.tail
      have h := hword (d::w) hd
      have hid : (a*b.val-t.functional (a*b.val) • (1:A))*word w =
          a*word (b::w)-t.functional (a*b.val) • word w := by
        simp only [word_cons,sub_mul,smul_mul_assoc,one_mul,mul_assoc]
      have hj : α i (a*b.val-t.functional (a*b.val) • (1:A))*
            word (w.map (letter t S α hmem hτ)) =
          α i a*word ((b::w).map (letter t S α hmem hτ)) -
            t.functional (a*b.val) • word (w.map (letter t S α hmem hτ)) := by
        simp only [map_sub,map_smul,map_mul,map_one,List.map_cons,word_cons,letter_val,
          sub_mul,smul_mul_assoc,one_mul,mul_assoc,hib]
      change W (V ((a*b.val-t.functional (a*b.val) • (1:A))*word w)) =
        V (α i (a*b.val-t.functional (a*b.val) • (1:A))*
          word (w.map (letter t S α hmem hτ))) at h
      rw [hid,hj] at h
      simp only [map_sub,map_smul,ht] at h
      exact sub_left_inj.mp h
    · have hc : Reduced (c::b::w) := by
        exact List.isChain_cons_cons.mpr ⟨hib,hw⟩
      have ht := hword (b::w) hw
      have h := hword (c::b::w) hc
      change W (V ((a-t.functional a • (1:A))*word (b::w))) =
        V (α i (a-t.functional a • (1:A))*word ((b::w).map (letter t S α hmem hτ))) at h
      simp only [sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,map_one,ht] at h
      exact sub_left_inj.mp h

lemma action_left (i : ι) (a : A) (ha : a∈S i) :
    (action t S α hmem hτ hfree hgen).toContinuousLinearMap.comp (t.functional.gnsStarAlgHom a) =
    (t.functional.gnsStarAlgHom (α i a)).comp (action t S α hmem hτ hfree hgen).toContinuousLinearMap := by
  apply ext_reduced t S hfree hgen
  intro w hw
  simp only [ContinuousLinearMap.comp_apply,LinearIsometry.coe_toContinuousLinearMap,
    TracialGNS.algebraVector_apply,TracialGNS.left_coe]
  rw [action_word t S α hmem hτ hfree hgen w hw]
  rw [TracialGNS.left_coe]
  exact action_generator_word t S α hmem hτ hfree hgen i a ha w hw

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionBlock
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ k a, a∈S k → α k a∈S k)
  (hτ : ∀ k a, t.functional (α k a)=t.functional a)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma action_left_apply (k : ι) (a : A) (ha : a∈S k) (x : t.functional.GNS) :
    action t S α hmem hτ hfree hgen (t.functional.gnsStarAlgHom a x)=
      t.functional.gnsStarAlgHom (α k a) (action t S α hmem hτ hfree hgen x) :=
  congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS => T x)
    (action_left t S α hmem hτ hfree hgen k a ha)

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeNormalizer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_conj_generator (u : unitary D) (k : ι) (a : A) (ha : a∈S k) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv
      (t.functional.gnsStarAlgHom a) =
    t.functional.gnsStarAlgHom (innerFamily f i u k a) := by
  ext x
  let W := innerRepresentation t ht f S i hS hfree hgen u
  change W (t.functional.gnsStarAlgHom a (W.symm x))=_
  have h := action_left_apply t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen k a ha (W.symm x)
  change W (t.functional.gnsStarAlgHom a (W.symm x))=
    t.functional.gnsStarAlgHom (innerFamily f i u k a) (W (W.symm x)) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

lemma innerRepresentation_vacuum (u : unitary D) :
    innerRepresentation t ht f S i hS hfree hgen u (TracialGNS.vacuum t.functional)=
      TracialGNS.vacuum t.functional := by
  exact action_word t S (innerFamily f i u) (innerFamily_mem f S i hS u)
    (innerFamily_trace t ht f i u) hfree hgen [] reduced_nil

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCompactGroup
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace Kadison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_unitary_compact : IsCompact (unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ)) := by
  have hb : Bornology.IsBounded (unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ)) := by
    apply (Metric.isBounded_closedBall (x := (0 : Matrix ι ι ℂ)) (r := 1)).subset
    intro a ha
    rw [Metric.mem_closedBall,dist_zero_right]
    by_cases hι : Nonempty ι
    · let _ := hι
      exact (CStarRing.norm_coe_unitary (⟨a,ha⟩ : unitary (Matrix ι ι ℂ))).le
    · have : IsEmpty ι := not_nonempty_iff.mp hι
      have h : a=0 := Subsingleton.elim _ _
      rw [h,norm_zero]
      exact zero_le_one
  exact Metric.isCompact_of_isClosed_isBounded isClosed_unitary hb

instance matrixUnitaryCompactSpace : CompactSpace (unitary (Matrix ι ι ℂ)) :=
  isCompact_iff_compactSpace.mp matrix_unitary_compact

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_conj_mem_factor (u : unitary D)
    {a : t.functional.GNS →L[ℂ] t.functional.GNS} (ha : a∈factorOperators t f) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv a ∈ factorOperators t f := by
  obtain ⟨b,rfl⟩ := ha
  change (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv
    (t.functional.gnsStarAlgHom (f b)) ∈ factorOperators t f
  rw [innerRepresentation_conj_generator t ht f S i hS hfree hgen u i (f b)
    (by rw [hS]; exact ⟨b,rfl⟩),innerFamily_self]
  refine ⟨(u:D)*b*star (u:D),?_⟩
  change t.functional.gnsStarAlgHom (f ((u:D)*b*star (u:D)))=_
  simp only [map_mul,map_star]

end Kadison.FreeBlocks

namespace Kadison.TracialGNS

variable {D : Type*} [CStarAlgebra D]

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma stageUnitaryHom_continuous (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) : Continuous (stageUnitaryHom φ) := by
  exact (φ.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

end Kadison.TracialGNS

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)

variable (ε : ℝ) (hε : 0≤ε) (r : ℂ)

variable (hC : ∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
    (TracialGNS.vacuum t.functional) r x → ‖G*x-x*G‖≤ε*‖x‖)

variable (s : A) (hs : s∈S j) (hji : j≠i)

omit [PartialOrder D] [StarOrderedRing D] in
include he hGL hε hC hs hji in
theorem exists_free_symmetrization_oai : ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
    ‖V‖≤‖G‖ ∧
    (∀ n u, V*(innerRepresentation t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)=
      (innerRepresentation t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
    (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
    (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) r x → ‖V*x-x*V‖≤ε*‖x‖) ∧
    (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) r x → ‖V.adjoint*x-x*V.adjoint‖≤ε*‖x‖) ∧
    (baseSpace t S j).starProjection*(V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V)*
      (baseSpace t S j).starProjection=
    (baseSpace t S j).starProjection*(G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G)*
      (baseSpace t S j).starProjection := by
  let Γ := fun n : ℕ => ↥(unitary (Matrix (I n) (I n) ℂ))
  let : ∀ n, MeasurableSpace (Γ n) := fun n => borel (Γ n)
  let : ∀ n, BorelSpace (Γ n) := fun _ => ⟨rfl⟩
  let U : ∀ n, Γ n →* (t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS) := fun n =>
    (innerRepresentation t ht f S i hS hfree hgen).comp (TracialGNS.stageUnitaryHom (φ n))
  have hU : ∀ n x, Continuous fun g => U n g x := by
    intro n x
    exact (innerRepresentation_continuous t ht f S i hS hfree hgen x).comp
      (TracialGNS.stageUnitaryHom_continuous (φ n))
  have hnest : ∀ n m, n ≤ m → ∀ g : Γ n, ∃ k : Γ m, U m k=U n g := by
    intro n m h g
    refine ⟨TracialGNS.stageUnitary (e h) g,?_⟩
    apply congrArg (innerRepresentation t ht f S i hS hfree hgen)
    exact Subtype.ext (he n m h (g:Matrix (I n) (I n) ℂ))
  obtain ⟨V,hV,hVU,hVF,hVC,hVCs,hVQ⟩ := CornerSymmetrization.exists_symmetrization Γ U hU hnest
    (fun n => compactHaarProbability (Γ n)) (factorOperators t f) (ambientOperators t S)
    (TracialGNS.vacuum t.functional) r
    (fun n g => innerRepresentation_vacuum t ht f S i hS hfree hgen
      (TracialGNS.stageUnitary (φ n) g))
    (fun n g _ ha => innerRepresentation_conj_mem_factor t ht f S i hS hfree hgen
      (TracialGNS.stageUnitary (φ n) g) ha)
    (fun n g _ ha => (mem_ambientOperators t S).mpr
      (innerRepresentation_conj_mem_bicommutant t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) g) ((mem_ambientOperators t S).mp ha)))
    G ε hε (fun _ ⟨a,ha⟩ => by subst ha; exact hGL a) hC
    (baseSpace t S j).starProjection (t.functional.gnsStarAlgHom s)
    (isSelfAdjoint_starProjection _) 
    (fun n g => innerRepresentation_fixes_baseProjection t ht f S i j hS hfree hgen hji
      (TracialGNS.stageUnitary (φ n) g))
    (fun n g => innerRepresentation_commutes_other t ht f S i j hS hfree hgen hji
      (TracialGNS.stageUnitary (φ n) g) s hs)
  exact ⟨V,hV,hVU,(fun a => hVF _ ⟨a,rfl⟩),hVC,hVCs,hVQ⟩

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.FreeBlocks.exists_free_symmetrization_oai.{u_1, u_2} := @OAI.Kadison.FreeBlocks.exists_free_symmetrization_oai.{u_1, u_2}
