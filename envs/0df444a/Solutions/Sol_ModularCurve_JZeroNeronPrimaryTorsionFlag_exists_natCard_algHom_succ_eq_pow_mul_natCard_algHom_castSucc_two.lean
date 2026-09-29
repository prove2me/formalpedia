-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4406c9c4-a4ab-579e-a048-100498378ccd

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite WithConv
open scoped TensorProduct

namespace P2mFlagTowerCount

section Algebra

variable {R : Type*} [CommRing R]
variable {H B L : Type*} [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra R B]
  [CommRing L] [Algebra R L]

variable (L) in

noncomputable def precomp (π : H →ₐc[R] B) : WithConv (B →ₐ[R] L) →* WithConv (H →ₐ[R] L) where
  toFun g := toConv (g.ofConv.comp (π : H →ₐ[R] B))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    refine WithConv.ext ?_
    exact AlgHom.convMul_comp_bialgHom_distrib f g π

lemma precomp_injective (π : H →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Injective (precomp L π) := by
  intro g₁ g₂ h
  refine WithConv.ext (AlgHom.ext fun b => ?_)
  obtain ⟨x, rfl⟩ := hπ b
  exact congrArg (fun t : WithConv (H →ₐ[R] L) => t x) h

noncomputable def antipodeAlgHom (C : Type*) [CommRing C] [HopfAlgebra R C] : C →ₐ[R] C :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R (A := C)) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

@[scoped simp] lemma antipodeAlgHom_apply (C : Type*) [CommRing C] [HopfAlgebra R C] (c : C) :
    antipodeAlgHom (R := R) C c = HopfAlgebra.antipode R c := rfl

lemma antipode_convMul {C : Type*} [CommRing C] [HopfAlgebra R C] (g : C →ₐ[R] L) :
    toConv (g.comp (antipodeAlgHom (R := R) C)) * toConv g = 1 := by
  refine WithConv.ext (AlgHom.ext fun c => ?_)
  change (toConv (g.comp (antipodeAlgHom (R := R) C)) * toConv g) c =
    (1 : WithConv (C →ₐ[R] L)) c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R c
  rw [← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, antipodeAlgHom_apply]
  rw [← g.commutes, ← HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit ℛ, map_sum]
  simp only [map_mul]

lemma convMul_antipode {C : Type*} [CommRing C] [HopfAlgebra R C] (g : C →ₐ[R] L) :
    toConv g * toConv (g.comp (antipodeAlgHom (R := R) C)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun c => ?_)
  change (toConv g * toConv (g.comp (antipodeAlgHom (R := R) C))) c =
    (1 : WithConv (C →ₐ[R] L)) c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  let ℛ := Coalgebra.Repr.arbitrary R c
  rw [← ℛ.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    Function.comp_apply, antipodeAlgHom_apply]
  rw [← g.commutes, ← HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit ℛ, map_sum]
  simp only [map_mul]

noncomputable def unitOfPoint {C : Type*} [CommRing C] [HopfAlgebra R C]
    (φ : WithConv (C →ₐ[R] L)) : (WithConv (C →ₐ[R] L))ˣ where
  val := φ
  inv := toConv (φ.ofConv.comp (antipodeAlgHom (R := R) C))
  val_inv := by simpa using convMul_antipode (R := R) (L := L) φ.ofConv
  inv_val := by simpa using antipode_convMul (R := R) (L := L) φ.ofConv

variable (L) in

lemma natCard_units_withConv (C : Type*) [CommRing C] [HopfAlgebra R C] :
    Nat.card (WithConv (C →ₐ[R] L))ˣ = Nat.card (C →ₐ[R] L) := by
  have hb : Function.Bijective (Units.val : (WithConv (C →ₐ[R] L))ˣ → WithConv (C →ₐ[R] L)) :=
    ⟨fun _ _ h => Units.ext h, fun φ => ⟨unitOfPoint φ, rfl⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hb)).trans (Nat.card_congr (WithConv.equiv _))

lemma natCard_algHom_dvd_of_surjective (π : H →ₐc[R] B) (hπ : Function.Surjective π) :
    Nat.card (B →ₐ[R] L) ∣ Nat.card (H →ₐ[R] L) := by
  let ψ : (WithConv (B →ₐ[R] L))ˣ →* (WithConv (H →ₐ[R] L))ˣ := Units.map (precomp L π)
  have hψ : Function.Injective ψ := by
    intro u v h
    exact Units.ext (precomp_injective π hπ (congrArg Units.val h))
  have h1 : Nat.card ψ.range = Nat.card (B →ₐ[R] L) := by
    rw [← natCard_units_withConv (R := R) L B]
    exact Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm
  rw [← h1, ← natCard_units_withConv (R := R) L H]
  exact Subgroup.card_subgroup_dvd_card ψ.range

end Algebra

section Yoneda

variable {R : Type*} [CommRing R]
variable {H B : Type*} [CommRing H] [HopfAlgebra R H] [CommRing B] [HopfAlgebra R B]

open Algebra.TensorProduct in

lemma convMul_includeLeft_includeRight :
    (toConv (includeLeft : B →ₐ[R] B ⊗[R] B) * toConv (includeRight : B →ₐ[R] B ⊗[R] B)).ofConv
      = Bialgebra.comulAlgHom R B := by
  rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc, lmul'_comp_map,
    lift_includeLeft_includeRight, AlgHom.id_comp]

open Algebra.TensorProduct in
lemma convMul_includeLeft_comp_includeRight_comp (π : H →ₐ[R] B) :
    (toConv ((includeLeft : B →ₐ[R] B ⊗[R] B).comp π)
        * toConv ((includeRight : B →ₐ[R] B ⊗[R] B).comp π)).ofConv
      = (map π π).comp (Bialgebra.comulAlgHom R H) := by
  rw [AlgHom.convMul_def, ofConv_toConv, map_comp, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc,
    lmul'_comp_map, lift_includeLeft_includeRight, AlgHom.id_comp]

theorem exists_bialgHom_of_convMul (π : H →ₐ[R] B)
    (hmul : ∀ g₁ g₂ : WithConv (B →ₐ[R] B ⊗[R] B),
      (g₁ * g₂).ofConv.comp π = (toConv (g₁.ofConv.comp π) * toConv (g₂.ofConv.comp π)).ofConv)
    (hone : (1 : WithConv (B →ₐ[R] B ⊗[R] B)).ofConv.comp π
      = (1 : WithConv (H →ₐ[R] B ⊗[R] B)).ofConv) :
    ∃ πc : H →ₐc[R] B, (πc : H →ₐ[R] B) = π := by

  have hΔ : (Algebra.TensorProduct.map π π).comp (Bialgebra.comulAlgHom R H)
      = (Bialgebra.comulAlgHom R B).comp π := by
    have h := hmul (toConv Algebra.TensorProduct.includeLeft)
      (toConv Algebra.TensorProduct.includeRight)
    rw [ofConv_toConv, ofConv_toConv, convMul_includeLeft_includeRight,
      convMul_includeLeft_comp_includeRight_comp] at h
    exact h.symm

  have hε : (Bialgebra.counitAlgHom R B).comp π = Bialgebra.counitAlgHom R H := by
    set χ : B ⊗[R] B →ₐ[R] R :=
      (Bialgebra.counitAlgHom R B).comp (Algebra.TensorProduct.lmul' R)
    have h := congrArg (fun f : H →ₐ[R] B ⊗[R] B => χ.comp f) hone
    have hχ : χ.comp (Algebra.ofId R (B ⊗[R] B)) = AlgHom.id R R := Subsingleton.elim _ _
    rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ofConv_toConv,
      ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hχ, AlgHom.id_comp, ← AlgHom.comp_assoc, hχ,
      AlgHom.id_comp] at h
    exact h
  exact ⟨BialgHom.ofAlgHom π hε hΔ, rfl⟩

variable {Γ T : Type*} [CommRing Γ] [Algebra R Γ] [CommRing T] [Algebra R T]

lemma convMul_comp_transport (ep : Γ →ₐ[R] T) (em : T →ₐ[R] Γ) (he : ep.comp em = AlgHom.id R T)
    (π : H →ₐ[R] B)
    (hmul : ∀ g₁ g₂ : WithConv (B →ₐ[R] Γ),
      (g₁ * g₂).ofConv.comp π = (toConv (g₁.ofConv.comp π) * toConv (g₂.ofConv.comp π)).ofConv)
    (g₁ g₂ : WithConv (B →ₐ[R] T)) :
    (g₁ * g₂).ofConv.comp π = (toConv (g₁.ofConv.comp π) * toConv (g₂.ofConv.comp π)).ofConv := by
  have hee : ∀ f : B →ₐ[R] T, ep.comp (em.comp f) = f := fun f => by
    rw [← AlgHom.comp_assoc, he, AlgHom.id_comp]
  have hee' : ∀ f : H →ₐ[R] T, ep.comp (em.comp f) = f := fun f => by
    rw [← AlgHom.comp_assoc, he, AlgHom.id_comp]
  have h := congrArg (fun f : H →ₐ[R] Γ => ep.comp f)
    (hmul (toConv (em.comp g₁.ofConv)) (toConv (em.comp g₂.ofConv)))
  dsimp only at h
  rw [← AlgHom.comp_assoc, AlgHom.comp_convMul_distrib, AlgHom.comp_convMul_distrib,
    ofConv_toConv, ofConv_toConv, hee, hee, toConv_ofConv, toConv_ofConv,
    AlgHom.comp_assoc, AlgHom.comp_assoc, hee', hee'] at h
  exact h

lemma convOne_comp_transport (ep : Γ →ₐ[R] T) (π : H →ₐ[R] B)
    (hone : (1 : WithConv (B →ₐ[R] Γ)).ofConv.comp π = (1 : WithConv (H →ₐ[R] Γ)).ofConv) :
    (1 : WithConv (B →ₐ[R] T)).ofConv.comp π = (1 : WithConv (H →ₐ[R] T)).ofConv := by
  have h := congrArg (fun f : H →ₐ[R] Γ => ep.comp f) hone
  have he : ep.comp (Algebra.ofId R Γ) = Algebra.ofId R T := Subsingleton.elim _ _
  rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ofConv_toConv,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, he, ← AlgHom.comp_assoc, he] at h
  rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ofConv_toConv]
  exact h

lemma flat_algebraMap_tensor [Module.Flat R B] : (algebraMap R (B ⊗[R] B)).Flat := by
  rw [RingHom.flat_algebraMap_iff]; infer_instance

lemma finitePresentation_algebraMap_tensor [IsNoetherianRing R] [Algebra.FiniteType R B] :
    (algebraMap R (B ⊗[R] B)).FinitePresentation := by
  rw [RingHom.finitePresentation_algebraMap]
  have : Algebra.FiniteType R (B ⊗[R] B) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact Algebra.FinitePresentation.of_finiteType.mp this

end Yoneda

section SpecObj

lemma flat_int_irrel {T : Type*} [AddCommGroup T] {i₁ i₂ : Module ℤ T}
    (h : @Module.Flat ℤ T _ _ i₁) : @Module.Flat ℤ T _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

variable {T : Type} [CommRing T] {instT : Algebra ℤ T}

variable (T) in

noncomputable def specHom : Spec (CommRingCat.of T) ⟶ specInt :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ T))

noncomputable def specObj (hf : (algebraMap ℤ T).Flat) (hp : (algebraMap ℤ T).FinitePresentation) :
    specInt.Fppf :=
  @Scheme.Fppf.mk _ _ (specHom T)
    (by rw [specHom, HasRingHomProperty.Spec_iff (P := @Flat)]; exact hf)
    (by rw [specHom, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]; exact hp)

def intAlgHom {A B : Type*} [CommRing A] [CommRing B] {_ : Algebra ℤ A} {_ : Algebra ℤ B}
    (f : A →+* B) : A →ₐ[ℤ] B :=
  { f with commutes' := fun z => by simp }

section Gamma

variable (hf : (algebraMap ℤ T).Flat) (hp : (algebraMap ℤ T).FinitePresentation)

noncomputable def gammaTo : Γ((specObj hf hp).left, ⊤) →ₐ[ℤ] T :=
  intAlgHom (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.toRingHom

noncomputable def gammaFrom : T →ₐ[ℤ] Γ((specObj hf hp).left, ⊤) :=
  intAlgHom (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.symm.toRingHom

lemma gammaTo_comp_gammaFrom : (gammaTo hf hp).comp (gammaFrom hf hp) = AlgHom.id ℤ T := by
  ext t
  exact (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv.apply_symm_apply t

end Gamma

variable {H B : Type} [CommRing H] [HopfAlgebra ℤ H] [CommRing B] [HopfAlgebra ℤ B]

lemma convMul_comp_of_fppf (hf : (algebraMap ℤ T).Flat) (hp : (algebraMap ℤ T).FinitePresentation)
    (π : H →ₐ[ℤ] B)
    (hmul : ∀ (U : specInt.Fppf) (g₁ g₂ : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))),
      (g₁ * g₂).ofConv.comp π = (toConv (g₁.ofConv.comp π) * toConv (g₂.ofConv.comp π)).ofConv)
    (g₁ g₂ : WithConv (B →ₐ[ℤ] T)) :
    (g₁ * g₂).ofConv.comp π = (toConv (g₁.ofConv.comp π) * toConv (g₂.ofConv.comp π)).ofConv :=
  convMul_comp_transport (gammaTo hf hp) (gammaFrom hf hp) (gammaTo_comp_gammaFrom hf hp) π
    (hmul (specObj hf hp)) g₁ g₂

lemma convOne_comp_of_fppf (hf : (algebraMap ℤ T).Flat) (hp : (algebraMap ℤ T).FinitePresentation)
    (π : H →ₐ[ℤ] B)
    (hone : ∀ U : specInt.Fppf,
      (1 : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))).ofConv.comp π
        = (1 : WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))).ofConv) :
    (1 : WithConv (B →ₐ[ℤ] T)).ofConv.comp π = (1 : WithConv (H →ₐ[ℤ] T)).ofConv :=
  convOne_comp_transport (gammaTo hf hp) π (hone (specObj hf hp))

end SpecObj

theorem exists_bialgHom_of_forall_fppf {H B : Type} [CommRing H] [HopfAlgebra ℤ H]
    [CommRing B] [HopfAlgebra ℤ B]
    (hflat : @Module.Flat ℤ B _ _ Algebra.toModule) [Algebra.FiniteType ℤ B]
    (π : H →ₐ[ℤ] B)
    (hmul : ∀ (U : specInt.Fppf) (g₁ g₂ : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))),
      (g₁ * g₂).ofConv.comp π = (toConv (g₁.ofConv.comp π) * toConv (g₂.ofConv.comp π)).ofConv)
    (hone : ∀ U : specInt.Fppf,
      (1 : WithConv (B →ₐ[ℤ] Γ(U.left, ⊤))).ofConv.comp π
        = (1 : WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))).ofConv) :
    ∃ πc : H →ₐc[ℤ] B, (πc : H →ₐ[ℤ] B) = π :=
  haveI := hflat
  exists_bialgHom_of_convMul π
    (convMul_comp_of_fppf flat_algebraMap_tensor finitePresentation_algebraMap_tensor π hmul)
    (convOne_comp_of_fppf flat_algebraMap_tensor finitePresentation_algebraMap_tensor π hone)

section Flag

open ModularCurve ValuationSubring

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {hA : A.LiesOverPrime p} {C : JZeroNeronPrimaryTorsionCore p q A hA} {m : ℕ}
  (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

lemma sections_compat (j : Fin (flag.n + 1)) (U : specInt.Fppf) (s : (flag.F j).1.obj (op U)) :
    (Additive.toMul (C.sectionsEquiv m U ((flag.ι j).1.app (op U) s))).ofConv
      = (Additive.toMul (flag.F_sectionsEquiv j U s)).ofConv.comp (flag.π j) :=
  AlgHom.ext fun h => flag.F_sectionsCompat j U s h

lemma comp_pi_convMul (j : Fin (flag.n + 1)) (U : specInt.Fppf)
    (g₁ g₂ : WithConv (flag.G j →ₐ[ℤ] Γ(U.left, ⊤))) :
    (g₁ * g₂).ofConv.comp (flag.π j)
      = (toConv (g₁.ofConv.comp (flag.π j)) * toConv (g₂.ofConv.comp (flag.π j))).ofConv := by
  set E := flag.F_sectionsEquiv j U with hE
  set s₁ := E.symm (Additive.ofMul g₁) with hs₁
  set s₂ := E.symm (Additive.ofMul g₂) with hs₂
  have hg₁ : Additive.toMul (E s₁) = g₁ := by simp [hs₁]
  have hg₂ : Additive.toMul (E s₂) = g₂ := by simp [hs₂]
  have h12 : Additive.toMul (E (s₁ + s₂)) = g₁ * g₂ := by rw [map_add, toMul_add, hg₁, hg₂]
  have k₁ : Additive.toMul (C.sectionsEquiv m U ((flag.ι j).1.app (op U) s₁))
      = toConv (g₁.ofConv.comp (flag.π j)) :=
    WithConv.ext (by rw [ofConv_toConv, sections_compat, ← hE, hg₁])
  have k₂ : Additive.toMul (C.sectionsEquiv m U ((flag.ι j).1.app (op U) s₂))
      = toConv (g₂.ofConv.comp (flag.π j)) :=
    WithConv.ext (by rw [ofConv_toConv, sections_compat, ← hE, hg₂])
  calc (g₁ * g₂).ofConv.comp (flag.π j)
      = (Additive.toMul (E (s₁ + s₂))).ofConv.comp (flag.π j) := by rw [h12]
    _ = (Additive.toMul (C.sectionsEquiv m U ((flag.ι j).1.app (op U) (s₁ + s₂)))).ofConv := by
          rw [sections_compat, ← hE]
    _ = (Additive.toMul (C.sectionsEquiv m U ((flag.ι j).1.app (op U) s₁))
          * Additive.toMul (C.sectionsEquiv m U ((flag.ι j).1.app (op U) s₂))).ofConv := by
          rw [map_add, map_add, toMul_add]
    _ = (toConv (g₁.ofConv.comp (flag.π j)) * toConv (g₂.ofConv.comp (flag.π j))).ofConv := by
          rw [k₁, k₂]

lemma comp_pi_convOne (j : Fin (flag.n + 1)) (U : specInt.Fppf) :
    (1 : WithConv (flag.G j →ₐ[ℤ] Γ(U.left, ⊤))).ofConv.comp (flag.π j)
      = (1 : WithConv (C.H m →ₐ[ℤ] Γ(U.left, ⊤))).ofConv := by
  have h := sections_compat flag j U 0
  have h1 : C.sectionsEquiv m U ((flag.ι j).1.app (op U) (0 : (flag.F j).1.obj (op U))) = 0 := by
    rw [map_zero, map_zero]
  have h2 : flag.F_sectionsEquiv j U (0 : (flag.F j).1.obj (op U)) = 0 := map_zero _
  rw [h1, h2, toMul_zero, toMul_zero] at h
  exact h.symm

theorem exists_bialgHom_pi (j : Fin (flag.n + 1)) :
    ∃ πc : C.H m →ₐc[ℤ] flag.G j, (πc : C.H m →ₐ[ℤ] flag.G j) = flag.π j :=
  exists_bialgHom_of_forall_fppf (flat_int_irrel (flag.instFlat_G j)) (flag.π j)
    (comp_pi_convMul flag j) (comp_pi_convOne flag j)

theorem natCard_algHom_G_dvd (j : Fin (flag.n + 1)) (L : Type*) [CommRing L] [Algebra ℤ L] :
    Nat.card (flag.G j →ₐ[ℤ] L) ∣ Nat.card (C.H m →ₐ[ℤ] L) := by
  obtain ⟨πc, hπc⟩ := exists_bialgHom_pi flag j
  refine natCard_algHom_dvd_of_surjective πc ?_
  have : (πc : C.H m → flag.G j) = flag.π j := by
    funext x; exact congrArg (fun f : C.H m →ₐ[ℤ] flag.G j => f x) hπc
  rw [this]; exact flag.π_surj j

theorem natCard_algHom_castSucc_le (i : Fin flag.n) (L : Type*) [CommRing L] [Algebra ℤ L]
    [Finite (flag.G i.succ →ₐ[ℤ] L)] :
    Nat.card (flag.G i.castSucc →ₐ[ℤ] L) ≤ Nat.card (flag.G i.succ →ₐ[ℤ] L) := by
  refine Nat.card_le_card_of_injective (fun g => g.comp (flag.quot i)) ?_
  intro g₁ g₂ h
  refine AlgHom.ext fun b => ?_
  obtain ⟨x, rfl⟩ := flag.quot_surj i b
  exact congrArg (fun t : flag.G i.succ →ₐ[ℤ] L => t x) h

end Flag

end P2mFlagTowerCount
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two.P2mFlagTowerCount"

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p 2 A hA C m) (i : Fin flag.n) :
    ∃ da : ℕ,
      Nat.card (flag.G i.succ →ₐ[ℤ] AlgebraicClosure (ZMod 2))
        = 2 ^ da * Nat.card (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure (ZMod 2)) := by
  obtain ⟨a, ha⟩ :=
    JZeroNeronPrimaryTorsionCore.exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow p A hA C m
  have key : ∀ j : Fin (flag.n + 1),
      ∃ c : ℕ, Nat.card (flag.G j →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ c := fun j => by
    have h := P2mFlagTowerCount.natCard_algHom_G_dvd flag j (AlgebraicClosure (ZMod 2))
    rw [ha, Nat.dvd_prime_pow Nat.prime_two] at h
    obtain ⟨c, -, hc⟩ := h
    exact ⟨c, hc⟩
  obtain ⟨b, hb⟩ := key i.succ
  obtain ⟨c, hc⟩ := key i.castSucc
  haveI : Finite (flag.G i.succ →ₐ[ℤ] AlgebraicClosure (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hb]; positivity)
  have hle := P2mFlagTowerCount.natCard_algHom_castSucc_le flag i (AlgebraicClosure (ZMod 2))
  rw [hb, hc] at hle
  have hcb : c ≤ b := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  refine ⟨b - c, ?_⟩
  rw [hb, hc, ← pow_add, Nat.sub_add_cancel hcb]

end S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two (solution)
