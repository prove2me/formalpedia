-- Prove2me | solution 1 for MasulloGRH.nuclear_of_separated_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T22:50:35.964063+00:00
-- url     : https://prove2.me/submissions/837f9e20-24fc-4b6d-8fb2-82caab2ef018

import Theorems.Thm_MasulloGRH_nuclear_quotient
import Theorems.Thm_MasulloGRH_nuclear_of_l1_tensor_topologies_eq

set_option autoImplicit false

open MasulloGRH Topology TopologicalSpace TensorProduct

private theorem locallyConvex_induced {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {t : TopologicalSpace B} (ht : IsLocallyConvexTopology B t) (f : A →ₗ[ℂ] B) :
    IsLocallyConvexTopology A (induced f t) := by
  let : TopologicalSpace B := t
  let : TopologicalSpace A := induced f t
  obtain ⟨_, _, _, hp⟩ := ht
  have : PolynormableSpace ℂ A := (f.withSeminorms_induced hp).toPolynormableSpace
  exact ⟨_, ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ A⟩

section

universe u₁ u₂
variable {A F : Type u₁} {B H : Type u₂}
  [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
  [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]

private theorem projective_admissible_pullback
    (e : A ≃L[ℂ] B) (f : F ≃L[ℂ] H) (t : TopologicalSpace (B ⊗[ℂ] H))
    (ht : IsLocallyConvexTopology (B ⊗[ℂ] H) t ∧
      @Continuous (B × H) (B ⊗[ℂ] H) _ t (fun p => p.1 ⊗ₜ[ℂ] p.2)) :
    let g := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
    IsLocallyConvexTopology (A ⊗[ℂ] F) (induced g t) ∧
      @Continuous (A × F) (A ⊗[ℂ] F) _ (induced g t) (fun p => p.1 ⊗ₜ[ℂ] p.2) := by
  dsimp only
  constructor
  · exact locallyConvex_induced ht.1
      (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv).toLinearMap
  · apply continuous_induced_rng.mpr
    simpa only [Function.comp_def, TensorProduct.congr_tmul,
      ContinuousLinearEquiv.coe_toLinearEquiv] using
      ht.2.comp ((e.continuous.comp continuous_fst).prodMk (f.continuous.comp continuous_snd))

-- Pullback gives a bijection between the topologies admissible in the two projective definitions.
private theorem projective_induced (e : A ≃L[ℂ] B) (f : F ≃L[ℂ] H) :
    projTensorTopology A F =
      induced (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
        (projTensorTopology B H) := by
  rw [projTensorTopology, projTensorTopology, induced_sInf]
  congr 1
  ext t
  constructor
  · intro ht
    let g := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
    refine ⟨induced g.symm t, ?_, ?_⟩
    · have hg : g.symm = TensorProduct.congr e.symm.toLinearEquiv f.symm.toLinearEquiv := by
        dsimp only [g]
        rw [TensorProduct.congr_symm]
        rfl
      rw [hg]
      exact projective_admissible_pullback e.symm f.symm t ht
    · change induced g (induced g.symm t) = t
      rw [induced_compose]
      have h : (g.symm : _ → _) ∘ g = id := funext g.symm_apply_apply
      rw [h, induced_id]
  · rintro ⟨t, ht, rfl⟩
    exact projective_admissible_pullback e f t ht

private def equicontinuousProducts (A F : Type u₁)
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :
    Set (Set (StrongDual ℂ A × StrongDual ℂ F)) :=
  {S | ∃ (U : Set (StrongDual ℂ A)) (V : Set (StrongDual ℂ F)),
    Equicontinuous (fun a : U => (a : A → ℂ)) ∧
    Equicontinuous (fun b : V => (b : F → ℂ)) ∧ S = U ×ˢ V}

private theorem equicontinuous_precomp_image {K L : Type*}
    [AddCommGroup K] [Module ℂ K] [TopologicalSpace K]
    [AddCommGroup L] [Module ℂ L] [TopologicalSpace L]
    (l : K →L[ℂ] L) {U : Set (StrongDual ℂ L)}
    (hU : Equicontinuous (fun a : U => (a : L → ℂ))) :
    Equicontinuous (fun a : (fun a : StrongDual ℂ L => a.comp l) '' U => (a : K → ℂ)) := by
  classical
  let pull (a : StrongDual ℂ L) := a.comp l
  have hcomp : Equicontinuous (fun a : U => ((a : L → ℂ) ∘ l)) := by
    rw [equicontinuous_iff_continuous] at hU ⊢
    exact hU.comp l.continuous
  change Equicontinuous (fun a : pull '' U => (a : K → ℂ))
  let lift (a : pull '' U) : U := ⟨a.property.choose, a.property.choose_spec.1⟩
  have hlift (a : pull '' U) : pull (lift a) = a := a.property.choose_spec.2
  convert hcomp.comp lift using 1
  funext a x
  exact (congrArg (fun b : StrongDual ℂ K => b x) (hlift a)).symm

private theorem eps_continuous (e : A ≃L[ℂ] B) (f : F ≃L[ℂ] H) :
    @Continuous (A ⊗[ℂ] F) (B ⊗[ℂ] H) (epsTensorTopology A F) (epsTensorTopology B H)
      (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) := by
  let pull (l : StrongDual ℂ B) : StrongDual ℂ A := l.comp e.toContinuousLinearMap
  let pull' (l : StrongDual ℂ H) : StrongDual ℂ F := l.comp f.toContinuousLinearMap
  let pullPair := Prod.map pull pull'
  have hmaps : Set.MapsTo (fun S => pullPair '' S)
      (equicontinuousProducts B H) (equicontinuousProducts A F) := by
    rintro S ⟨U, V, hU, hV, rfl⟩
    refine ⟨pull '' U, pull' '' V, equicontinuous_precomp_image _ hU,
      equicontinuous_precomp_image _ hV, ?_⟩
    ext ab
    constructor
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    · rintro ⟨⟨a, ha, hea⟩, ⟨b, hb, heb⟩⟩
      exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext hea heb⟩
  let evalA (t : A ⊗[ℂ] F) :=
    UniformOnFun.ofFun (equicontinuousProducts A F) (tensorFunctional A F · t)
  let evalB (t : B ⊗[ℂ] H) :=
    UniformOnFun.ofFun (equicontinuousProducts B H) (tensorFunctional B H · t)
  let g := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  let pre (f : UniformOnFun _ ℂ (equicontinuousProducts A F)) :=
    UniformOnFun.ofFun (equicontinuousProducts B H)
      (UniformOnFun.toFun (equicontinuousProducts A F) f ∘ pullPair)
  have hpre : Continuous pre := (UniformOnFun.precomp_uniformContinuous hmaps).continuous
  change @Continuous _ _ (induced evalA _) (induced evalB _) g
  apply continuous_induced_rng.mpr
  -- Evaluating a mapped tensor is evaluation against the pulled-back functionals.
  have heval : evalB ∘ g = pre ∘ evalA := by
    funext t
    change UniformOnFun.ofFun _ _ = UniformOnFun.ofFun _ _
    congr 1
    funext ab
    change tensorFunctional B H ab (g t) = tensorFunctional A F (pullPair ab) t
    induction t using TensorProduct.induction_on with
    | zero => simp [tensorFunctional]
    | tmul a b =>
      simp [g, tensorFunctional, pullPair, pull, pull']
    | add t v ht hv => simpa only [tensorFunctional, map_add] using congrArg₂ (· + ·) ht hv
  rw [heval]
  have hEvalA : @Continuous _ _ (induced evalA inferInstance) inferInstance evalA :=
    continuous_induced_dom
  exact @Continuous.comp _ _ _ (induced evalA inferInstance) _ _ _ _ hpre hEvalA

private theorem tensor_topologies_eq_of_equiv (e : A ≃L[ℂ] B) (f : F ≃L[ℂ] H)
    (hA : projTensorTopology A F = epsTensorTopology A F) :
    projTensorTopology B H = epsTensorTopology B H := by
  let g := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  have hforward := continuous_iff_le_induced.mp (eps_continuous e f)
  have hbackward := continuous_iff_le_induced.mp (eps_continuous e.symm f.symm)
  have hg : epsTensorTopology A F = induced g (epsTensorTopology B H) := by
    refine le_antisymm hforward ?_
    have h := induced_mono (g := (g : (A ⊗[ℂ] F) → (B ⊗[ℂ] H))) hbackward
    change induced g (epsTensorTopology B H) ≤ induced g (induced g.symm (epsTensorTopology A F)) at h
    have hcomp : (g.symm : _ → _) ∘ g = id := funext g.symm_apply_apply
    rwa [induced_compose, hcomp, @induced_id _ (epsTensorTopology A F)] at h
  have h := (projective_induced e f).symm.trans (hA.trans hg)
  have hcomp : (g : _ → _) ∘ g.symm = id := funext g.apply_symm_apply
  change induced g (projTensorTopology B H) = induced g (epsTensorTopology B H) at h
  have h' := congrArg (induced (g.symm : (B ⊗[ℂ] H) → (A ⊗[ℂ] F))) h
  simpa only [induced_compose, hcomp, @induced_id _ (projTensorTopology B H),
    @induced_id _ (epsTensorTopology B H)] using h'
end

universe u v

theorem solution (G : Type u) (E : Type v) [AddCommGroup G] [Module ℂ G]
    [tG : TopologicalSpace G] [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
    (hG : IsNuclear G) (hE : IsHLCS E) (q : G →ₗ[ℂ] E) (hq : Function.Surjective q)
    (htop : tE = sInf {t | IsLocallyConvexTopology E t ∧ @Continuous G E tG t q}) :
    IsNuclear E := by
  have hq_cont : Continuous q := by
    apply continuous_iff_coinduced_le.mpr
    rw [htop]
    exact le_sInf (fun t ht => continuous_iff_coinduced_le.mp ht.2)
  have : T2Space E := hE.2
  let V := LinearMap.ker q
  have hclosed : IsClosed (V : Set G) := isClosed_singleton.preimage hq_cont
  have hV : IsNuclear (G ⧸ V) := nuclear_quotient G hG V hclosed
  let e : (G ⧸ V) ≃ₗ[ℂ] E := q.quotKerEquivOfSurjective hq
  have heq : (e : (G ⧸ V) → E) ∘ V.mkQ = q :=
    funext (q.quotKerEquivOfSurjective_apply_mk hq)
  have he : Continuous e := by
    apply V.isQuotientMap_mkQ.continuous_iff.mpr
    simpa only [heq] using hq_cont
  have hesymm : Continuous e.symm := by
    apply continuous_iff_le_induced.mpr
    rw [htop]
    refine sInf_le ⟨?_, ?_⟩
    · exact locallyConvex_induced hV.1.1 e.symm.toLinearMap
    · apply continuous_induced_rng.mpr
      have hcomp : (e.symm : E → (G ⧸ V)) ∘ q = (V.mkQ : G → (G ⧸ V)) :=
        funext (q.quotKerEquivOfSurjective_symm_apply hq)
      rw [hcomp]
      exact V.continuous_mkQ
  let e' : (G ⧸ V) ≃L[ℂ] E := ⟨e, he, hesymm⟩
  let L := lp (fun _ : ℕ => ℂ) 1
  -- The nuclearity definition quantifies over test spaces in the same universe.
  let L₁ := ULift.{u} L
  let L₂ := ULift.{v} L
  have hL₁ : IsHLCS L₁ :=
    ⟨⟨_, ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ L₁⟩, inferInstance⟩
  have htest : projTensorTopology (G ⧸ V) L₁ = epsTensorTopology (G ⧸ V) L₁ := hV.2 L₁ hL₁
  let l₁ : L₁ ≃L[ℂ] L := ContinuousLinearEquiv.ulift
  let l₂ : L₂ ≃L[ℂ] L := ContinuousLinearEquiv.ulift
  exact nuclear_of_l1_tensor_topologies_eq E hE
    (tensor_topologies_eq_of_equiv e' (l₁.trans l₂.symm) htest)
