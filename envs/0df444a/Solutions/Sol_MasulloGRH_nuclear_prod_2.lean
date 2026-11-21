-- Prove2me | solution 2 for MasulloGRH.nuclear_prod
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T23:02:19.114285+00:00
-- url     : https://prove2.me/submissions/0592332e-cf35-42d1-95ee-ee632079609f

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH
open TensorProduct Topology

universe u

private lemma lc_induced {X Y : Type u} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (f : X →ₗ[ℂ] Y) (t : TopologicalSpace Y) (ht : IsLocallyConvexTopology Y t) :
    IsLocallyConvexTopology X (t.induced f) := by
  obtain ⟨ι, hι, p, hp⟩ := ht
  let _ := t
  exact ⟨ι, hι, p.comp f, f.withSeminorms_induced hp⟩

private lemma lc_continuousAdd {X : Type u} [AddCommGroup X] [Module ℂ X]
    (t : TopologicalSpace X) (ht : IsLocallyConvexTopology X t) : @ContinuousAdd X t _ := by
  obtain ⟨ι, hι, p, hp⟩ := ht
  let _ := t
  have := hp.topologicalAddGroup
  infer_instance

private lemma lc_prod {E G : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (hE : IsLocallyConvexTopology E ‹_›) (hG : IsLocallyConvexTopology G ‹_›) :
    IsLocallyConvexTopology (E × G) instTopologicalSpaceProd := by
  obtain ⟨ι, hι, p, hp⟩ := hE
  obtain ⟨κ, -, q, hq⟩ := hG
  let K : Bool → Type u := fun b => Bool.rec κ ι b
  let P : (b : Bool) → SeminormFamily ℂ (E × G) (K b) := fun b =>
    Bool.rec (q.comp (LinearMap.snd ℂ E G)) (p.comp (LinearMap.fst ℂ E G)) b
  let T : Bool → TopologicalSpace (E × G) := fun b =>
    Bool.rec (TopologicalSpace.induced (LinearMap.snd ℂ E G) ‹_›)
      (TopologicalSpace.induced (LinearMap.fst ℂ E G) ‹_›) b
  have h := withSeminorms_iInf (p := P) (t := T) (fun b => by
    cases b
    · exact (LinearMap.snd ℂ E G).withSeminorms_induced hq
    · exact (LinearMap.fst ℂ E G).withSeminorms_induced hp)
  have : (⨅ b, T b) = instTopologicalSpaceProd := by rw [iInf_bool_eq]; rfl
  rw [this] at h
  exact ⟨_, ⟨⟨true, Classical.arbitrary ι⟩⟩, _, h⟩

private lemma proj_map_continuous {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (F : Type u) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (L : X →L[ℂ] Y) :
    Continuous[projTensorTopology X F, projTensorTopology Y F]
      (TensorProduct.map (L : X →ₗ[ℂ] Y) (LinearMap.id : F →ₗ[ℂ] F)) := by
  refine continuous_sInf_rng.2 fun t ht => ?_
  refine continuous_sInf_dom (show t.induced (TensorProduct.map (L : X →ₗ[ℂ] Y)
    (LinearMap.id : F →ₗ[ℂ] F)) ∈ _ from ⟨lc_induced _ t ht.1, ?_⟩) continuous_induced_dom
  refine continuous_induced_rng.2 ?_
  have : ((TensorProduct.map (L : X →ₗ[ℂ] Y) (LinearMap.id : F →ₗ[ℂ] F)) ∘
      fun p : X × F => p.1 ⊗ₜ[ℂ] p.2) = (fun p : Y × F => p.1 ⊗ₜ[ℂ] p.2) ∘ Prod.map L id := by
    funext p; simp
  rw [this]
  exact ht.2.comp (L.continuous.prodMap continuous_id)

private lemma equicont_comp {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (L : X →L[ℂ] Y) (A : Set (StrongDual ℂ Y))
    (hA : Equicontinuous (fun a : A => (a : Y → ℂ))) :
    Equicontinuous (fun c : ((fun a : StrongDual ℂ Y => a.comp L) '' A) => (c : X → ℂ)) := by
  intro x₀ U hU
  refine ((L.continuous.tendsto x₀).eventually (hA (L x₀) U hU)).mono ?_
  rintro x hx ⟨c, a, ha, rfl⟩
  exact hx ⟨a, ha⟩

private def eqS (X F : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :
    Set (Set (StrongDual ℂ X × StrongDual ℂ F)) :=
  {S | ∃ (A : Set (StrongDual ℂ X)) (B : Set (StrongDual ℂ F)),
    Equicontinuous (fun a : A => (a : X → ℂ)) ∧ Equicontinuous (fun b : B => (b : F → ℂ)) ∧
      S = A ×ˢ B}

private lemma eps_eq (X F : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :
    epsTensorTopology X F = TopologicalSpace.induced
      (fun u : X ⊗[ℂ] F => UniformOnFun.ofFun (eqS X F) (fun ab => tensorFunctional X F ab u))
      inferInstance := rfl

private lemma eps_map_continuous {X Y : Type u} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (F : Type u) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (L : X →L[ℂ] Y) :
    Continuous[epsTensorTopology X F, epsTensorTopology Y F]
      (TensorProduct.map (L : X →ₗ[ℂ] Y) (LinearMap.id : F →ₗ[ℂ] F)) := by
  let f : StrongDual ℂ Y × StrongDual ℂ F → StrongDual ℂ X × StrongDual ℂ F :=
    fun ab => (ab.1.comp L, ab.2)
  have key : ∀ (ab : StrongDual ℂ Y × StrongDual ℂ F) (u : X ⊗[ℂ] F),
      tensorFunctional Y F ab (TensorProduct.map (L : X →ₗ[ℂ] Y) (LinearMap.id : F →ₗ[ℂ] F) u) =
        tensorFunctional X F (f ab) u := by
    intro ab u
    induction u using TensorProduct.induction_on with
    | zero => simp [tensorFunctional]
    | tmul x y => simp [tensorFunctional, f]
    | add x y hx hy =>
      simp only [tensorFunctional, map_add] at hx hy ⊢
      rw [hx, hy]
  rw [eps_eq Y F]
  refine continuous_induced_rng.2 ?_
  have hmaps : Set.MapsTo (f '' ·) (eqS Y F) (eqS X F) := by
    rintro S ⟨A, B, hA, hB, rfl⟩
    refine ⟨_, B, equicont_comp L A hA, hB, ?_⟩
    show Prod.map (fun a : StrongDual ℂ Y => a.comp L) id '' (A ×ˢ B) = _
    rw [Set.prodMap_image_prod, Set.image_id]
  let _ : TopologicalSpace (X ⊗[ℂ] F) := epsTensorTopology X F
  have hJ : Continuous
      (fun u : X ⊗[ℂ] F => UniformOnFun.ofFun (eqS X F) (fun ab => tensorFunctional X F ab u)) :=
    (continuous_iff_le_induced (t₁ := epsTensorTopology X F)).2 (le_of_eq (eps_eq X F))
  have := (UniformOnFun.precomp_uniformContinuous (β := ℂ) hmaps).continuous.comp hJ
  exact this.congr fun u => funext fun ab => (key ab u).symm

private lemma inf_eq {T A B : Type*} [AddCommGroup T] (tT : TopologicalSpace T)
    (tA : TopologicalSpace A) (tB : TopologicalSpace B) (hT : @ContinuousAdd T tT _)
    (p : T → A) (q : T → B) (i : A → T) (j : B → T) (hpq : ∀ u, i (p u) + j (q u) = u)
    (hp : Continuous[tT, tA] p) (hq : Continuous[tT, tB] q) (hi : Continuous[tA, tT] i)
    (hj : Continuous[tB, tT] j) :
    tT = tA.induced p ⊓ tB.induced q := by
  refine le_antisymm (le_inf (continuous_iff_le_induced.1 hp) (continuous_iff_le_induced.1 hq)) ?_
  rw [← continuous_id_iff_le]
  have hp' : Continuous[tA.induced p ⊓ tB.induced q, tA] p :=
    continuous_iff_le_induced.2 inf_le_left
  have hq' : Continuous[tA.induced p ⊓ tB.induced q, tB] q :=
    continuous_iff_le_induced.2 inf_le_right
  have h1 := @Continuous.add T tT _ hT T (tA.induced p ⊓ tB.induced q) (fun u => i (p u))
    (fun u => j (q u)) (@Continuous.comp T A T (tA.induced p ⊓ tB.induced q) tA tT p i hi hp')
      (@Continuous.comp T B T (tA.induced p ⊓ tB.induced q) tB tT q j hj hq')
  have h2 : (fun u => i (p u)) + (fun u => j (q u)) = id := funext hpq
  rw [h2] at h1
  exact h1

private lemma decomp {E G : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (F : Type u) [AddCommGroup F] [Module ℂ F]
    (τ : ∀ (X : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X],
      TopologicalSpace (X ⊗[ℂ] F))
    (hmap : ∀ (X Y : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y]
      [Module ℂ Y] [TopologicalSpace Y] (L : X →L[ℂ] Y),
      Continuous[τ X, τ Y] (TensorProduct.map (L : X →ₗ[ℂ] Y) (LinearMap.id : F →ₗ[ℂ] F)))
    (hadd : @ContinuousAdd _ (τ (E × G)) _) :
    τ (E × G) =
      (τ E).induced (TensorProduct.map ((ContinuousLinearMap.fst ℂ E G : E × G →L[ℂ] E) :
        E × G →ₗ[ℂ] E) (LinearMap.id : F →ₗ[ℂ] F)) ⊓
      (τ G).induced (TensorProduct.map ((ContinuousLinearMap.snd ℂ E G : E × G →L[ℂ] G) :
        E × G →ₗ[ℂ] G) (LinearMap.id : F →ₗ[ℂ] F)) := by
  refine inf_eq _ _ _ hadd _ _
    (TensorProduct.map ((ContinuousLinearMap.inl ℂ E G : E →L[ℂ] E × G) : E →ₗ[ℂ] E × G)
      (LinearMap.id : F →ₗ[ℂ] F))
    (TensorProduct.map ((ContinuousLinearMap.inr ℂ E G : G →L[ℂ] E × G) : G →ₗ[ℂ] E × G)
      (LinearMap.id : F →ₗ[ℂ] F)) ?_ (hmap _ _ _) (hmap _ _ _) (hmap _ _ _) (hmap _ _ _)
  intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    obtain ⟨a, b⟩ := x
    simp [← add_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    nth_rewrite 3 [← hx]
    nth_rewrite 3 [← hy]
    abel

private lemma eps_continuousAdd (X F : Type u) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :
    @ContinuousAdd _ (epsTensorTopology X F) _ := by
  let J : X ⊗[ℂ] F →+ UniformOnFun (StrongDual ℂ X × StrongDual ℂ F) ℂ (eqS X F) :=
    { toFun := fun u => UniformOnFun.ofFun (eqS X F) (fun ab => tensorFunctional X F ab u)
      map_zero' := by
        funext ab
        simp [tensorFunctional]
        rfl
      map_add' := by
        intro u v
        funext ab
        simp [tensorFunctional]
        rfl }
  rw [eps_eq]
  exact continuousAdd_induced J

theorem solution (E G : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] (hE : IsNuclear E) (hG : IsNuclear G) :
    IsNuclear (E × G) := by
  refine ⟨⟨lc_prod hE.1.1 hG.1.1, by have := hE.1.2; have := hG.1.2; infer_instance⟩, ?_⟩
  intro F _ _ _ hF
  rw [decomp F (fun X _ _ _ => projTensorTopology X F)
      (fun X Y _ _ _ _ _ _ L => proj_map_continuous F L)
      (continuousAdd_sInf fun t ht => lc_continuousAdd t ht.1),
    decomp F (fun X _ _ _ => epsTensorTopology X F)
      (fun X Y _ _ _ _ _ _ L => eps_map_continuous F L) (eps_continuousAdd _ F),
    hE.2 F hF, hG.2 F hF]

