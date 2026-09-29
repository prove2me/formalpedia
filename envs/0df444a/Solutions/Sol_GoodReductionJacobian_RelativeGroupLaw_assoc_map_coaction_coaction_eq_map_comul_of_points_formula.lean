-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.assoc_map_coaction_coaction_eq_map_comul_of_points_formula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/12c3ba2c-4b0c-5954-88e2-6a8817809d51

import Mathlib
import Theorems.Thm_AlgebraicGeometry_pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_assoc_map_coaction_coaction_eq_map_comul_of_points_formula

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

set_option synthInstance.maxHeartbeats 1600000 in

theorem CoassocAux.map_comul_eq {K S H : Type u} [CommRing K] [CommRing S] [CommRing H] [Algebra K S] [Bialgebra K H]
    (m : H →ₐ[K] S ⊗[K] (H ⊗[K] H)) (G : S ⊗[K] H →ₐ[K] S ⊗[K] (H ⊗[K] H))
    (hm : ∀ h : H, m h = (1 : S) ⊗ₜ[K] (Coalgebra.comul (R := K) h))
    (hG : ∀ (a : S) (h : H), G (a ⊗ₜ[K] h) = (Algebra.TensorProduct.includeLeft : S →ₐ[K] S ⊗[K] (H ⊗[K] H)) a * m h)
    (t : S ⊗[K] H) :
    Algebra.TensorProduct.map (AlgHom.id K S) (Bialgebra.comulAlgHom K H) t = G t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a h =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hG, Algebra.TensorProduct.includeLeft_apply, hm,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Bialgebra.comulAlgHom_apply]

theorem CoassocAux.assoc_map_eq {K S H : Type u} [CommRing K] [CommRing S] [CommRing H] [Algebra K S] [Algebra K H]
    (ρ : S →ₐ[K] S ⊗[K] H) (P F : S ⊗[K] H →ₐ[K] S ⊗[K] (H ⊗[K] H))
    (hP : ∀ (a : S) (h : H), P (a ⊗ₜ[K] h) =
      (Algebra.TensorProduct.includeLeft : S →ₐ[K] S ⊗[K] (H ⊗[K] H)) a *
        ((Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft : H →ₐ[K] S ⊗[K] (H ⊗[K] H))) h)
    (hF : ∀ (a : S) (h : H), F (a ⊗ₜ[K] h) =
      P (ρ a) * ((Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight : H →ₐ[K] S ⊗[K] (H ⊗[K] H))) h)
    (t : S ⊗[K] H) :
    (Algebra.TensorProduct.assoc K K K S H H) (Algebra.TensorProduct.map ρ (AlgHom.id K H) t) = F t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a h =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hF]
    induction (ρ a) using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero, zero_mul]
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, add_mul, hx, hy]
    | tmul a' h' =>
      rw [Algebra.TensorProduct.assoc_tmul, hP, AlgHom.comp_apply, AlgHom.comp_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeRight_apply]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (hsurj : Function.Surjective (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (act : pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ⟶ A)
    (hact : act ≫ f = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ f)
    (hpts : ∀ (T : Type u) [CommRing T] [Algebra K T]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f) (φ : WithConv (H →ₐ[K] T))
        (hx : x.1 ≫ f = Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K H))),
      pullback.lift x.1 (Spec.map (CommRingCat.ofHom (φ.ofConv : H →+* T))) hx ≫ act =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap K T))) x (e T φ).val).1)
    (hsh : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H))) ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n)
    (hiso : IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh))
    :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)))
    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hε_snd : ∀ (V : A.Opens) (hV : IsAffineOpen V) (h : H),
      ε V hV (((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).appLE ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of H)).inv.hom h)) =
        (1 : Γ(A, V)) ⊗ₜ[K] h)
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)))
    (ρ : ∀ U : A.affineOpens, Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))
    (U : A.affineOpens),
    ∀ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)),
        (Algebra.TensorProduct.assoc K K K _ H H) (Algebra.TensorProduct.map (ρ U) (AlgHom.id K H) (ρ U s)) =
          Algebra.TensorProduct.map (AlgHom.id K _) (Bialgebra.comulAlgHom K H) (ρ U s) := by
  intro hNaff ε hε_fst hε_res hε_snd hle ρ hρ U
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
  letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens,
      Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
  intro s

  have key : ∀ (T : Type u) [CommRing T] [Algebra K T] (α : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] T) (φ ψ : H →ₐ[K] T),
      ∃ (m : H →ₐ[K] T) (Q : H ⊗[K] H →ₐ[K] T) (P F G : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] H →ₐ[K] T),
        (∀ x y : H, Q (x ⊗ₜ[K] y) = φ x * ψ y) ∧
        (∀ h : H, m h = Q (Coalgebra.comul (R := K) h)) ∧
        (∀ (a : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) (h : H), P (a ⊗ₜ[K] h) = α a * φ h) ∧
        (∀ (a : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) (h : H), F (a ⊗ₜ[K] h) = P (ρ U a) * ψ h) ∧
        (∀ (a : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) (h : H), G (a ⊗ₜ[K] h) = α a * m h) ∧
        ∀ s : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)), F (ρ U s) = G (ρ U s) := by
    intro T _ _ α φ ψ
    let Φ : WithConv (H →ₐ[K] T) := WithConv.toConv φ
    let Ψ : WithConv (H →ₐ[K] T) := WithConv.toConv ψ
    let α₂ : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) →ₐ[K] T := (Algebra.TensorProduct.lift α φ (fun _ _ => Commute.all _ _)).comp (ρ U)
    refine ⟨(Φ * Ψ).ofConv, Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _),
      Algebra.TensorProduct.lift α φ (fun _ _ => Commute.all _ _),
      Algebra.TensorProduct.lift α₂ ψ (fun _ _ => Commute.all _ _),
      Algebra.TensorProduct.lift α (Φ * Ψ).ofConv (fun _ _ => Commute.all _ _),
      fun x y => Algebra.TensorProduct.lift_tmul _ _ _ x y,
      fun h => AlgHom.convMul_apply Φ Ψ h,
      fun a h => Algebra.TensorProduct.lift_tmul _ _ _ a h,
      fun a h => by rw [Algebra.TensorProduct.lift_tmul]; rfl,
      fun a h => by rw [Algebra.TensorProduct.lift_tmul], ?_⟩
    intro s

    obtain ⟨hfS, hx₁, hd₁⟩ :=
      AlgebraicGeometry.pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart K f H act hact
        ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) (hNaff U) (hle U) (ε _ (hNaff U)) (hε_fst _ (hNaff U)) (hε_snd _ (hNaff U))
        (ρ U) (hρ U) T α φ
    obtain ⟨-, hx₂, hd₂⟩ :=
      AlgebraicGeometry.pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart K f H act hact
        ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) (hNaff U) (hle U) (ε _ (hNaff U)) (hε_fst _ (hNaff U)) (hε_snd _ (hNaff U))
        (ρ U) (hρ U) T α₂ ψ
    obtain ⟨-, hx₃, hd₃⟩ :=
      AlgebraicGeometry.pullback_lift_comp_eq_specMap_lift_comp_comp_fromSpec_of_chart K f H act hact
        ((L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) (hNaff U) (hle U) (ε _ (hNaff U)) (hε_fst _ (hNaff U)) (hε_snd _ (hNaff U))
        (ρ U) (hρ U) T α (Φ * Ψ).ofConv

    let xα : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f :=
      ⟨Spec.map (CommRingCat.ofHom α.toRingHom) ≫ (hNaff U).fromSpec, by
        rw [Category.assoc, hfS, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]⟩
    let x₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f :=
      ⟨Spec.map (CommRingCat.ofHom α₂.toRingHom) ≫ (hNaff U).fromSpec, by
        rw [Category.assoc, hfS, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]⟩
    have hp₁ := hpts _ xα Φ hx₁
    have hp₂ := hpts _ x₂ Ψ hx₂
    have hp₃ := hpts _ xα (Φ * Ψ) hx₃

    have hA : L.mul _ xα (e _ Φ).val = x₂ := by
      apply Subtype.ext
      rw [← hp₁]; exact hd₁

    have hB : (L.mul _ (L.mul _ xα (e _ Φ).val) (e _ Ψ).val).1 =
        Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.lift α₂ ψ (fun _ _ => Commute.all _ _)).comp (ρ U)).toRingHom) ≫
          (hNaff U).fromSpec := by
      rw [hA, ← hp₂]; exact hd₂
    have hC : (L.mul _ (L.mul _ xα (e _ Φ).val) (e _ Ψ).val).1 =
        Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.lift α (Φ * Ψ).ofConv (fun _ _ => Commute.all _ _)).comp (ρ U)).toRingHom) ≫
          (hNaff U).fromSpec := by
      rw [L.mul_assoc, ← he_mul, ← hp₃]; exact hd₃
    have hBC := Spec.map_injective ((cancel_mono (hNaff U).fromSpec).mp (hB.symm.trans hC))
    have h4 := congrArg (fun χ : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⟶ CommRingCat.of T => χ.hom s) hBC
    simpa only [CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_comp, Function.comp_apply] using h4

  obtain ⟨m, Q, P, F, G, hQ, hm, hP, hF, hG, hkey⟩ := key (Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens)) ⊗[K] (H ⊗[K] H)) Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft)
    (Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight)
  have hm' : ∀ h : H, m h = (1 : Γ(A, (L.schemeNsmul n) ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] (Coalgebra.comul (R := K) h) := by
    intro h
    rw [hm h]
    induction (Coalgebra.comul (R := K) h) using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, TensorProduct.tmul_add]
    | tmul x y =>
      rw [hQ, AlgHom.comp_apply, AlgHom.comp_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [CoassocAux.assoc_map_eq (ρ U) P F hP hF, CoassocAux.map_comul_eq m G hm' hG]
  exact hkey s

end S_GoodReductionJacobian_RelativeGroupLaw_assoc_map_coaction_coaction_eq_map_comul_of_points_formula
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_assoc_map_coaction_coaction_eq_map_comul_of_points_formula (solution)
