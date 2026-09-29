-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/18fac98e-8814-559c-ab97-74ec6fa49f23

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_one_of_forall_withConv_point
import Theorems.Thm_BialgHom_exists_coe_eq_of_forall_withConv_comp
import Theorems.Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq

set_option autoImplicit false

open TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem aux_isReduced_baseChange_tensor_addMonoidAlgebra {A : Type} [CommRing A] (K : Type) [Field K] [CharZero K]
    [Algebra A K] (G : Type) [AddCommGroup G] [Finite G] :
    IsReduced (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G)) := by
  haveI : Module.Finite K (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G)) := inferInstance
  haveI : Algebra.FiniteType K (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G)) := Module.Finite.finiteType _
  exact HopfAlgebra.isReduced_of_finiteType_of_charZero K (K ⊗[A] (AddMonoidAlgebra A G ⊗[A] AddMonoidAlgebra A G))

theorem aux_noZeroSMulDivisors_of_free {A : Type} [CommRing A] [IsDomain A] (M : Type) [AddCommGroup M] [Module A M]
    [Module.Free A M] : NoZeroSMulDivisors A M := by
  classical
  refine ⟨fun {c x} h => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    apply (Module.Free.chooseBasis A M).repr.injective
    rw [map_zero]
    ext j
    have hj := congrArg (fun y => (Module.Free.chooseBasis A M).repr y j) h
    simp only [map_smul, Finsupp.smul_apply, map_zero, Finsupp.zero_apply, smul_eq_mul] at hj
    exact (mul_eq_zero.mp hj).resolve_left hc

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (i : Fin 2)
    (H : Type) [CommRing H] [HopfAlgebra ↥A H]
    (e : ∀ (T : Type) [CommRing T] [Algebra ↥A T],
      WithConv (H →ₐ[↥A] T) ≃
        (Λ.L.baseChange Λ.σA).torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap ↥A T))) m)
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra ↥A T] (φ ψ : WithConv (H →ₐ[↥A] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)) =
        (Λ.L.baseChange Λ.σA).mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra ↥A T] [CommRing T'] [Algebra ↥A T']
        (a : T →ₐ[↥A] T') (φ : WithConv (H →ₐ[↥A] T)),
      ((e T' (.toConv (a.comp φ.ofConv))).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e T φ).val.1) :
    ∃ φ : H →ₐc[↥A] muCoord ↥A O.toricRank m,
      ∀ (T : Type) [CommRing T] [Algebra ↥A T] (ψ : muCoord ↥A O.toricRank m →ₐ[↥A] T),
        ((e T (.toConv (ψ.comp (φ : H →ₐ[↥A] muCoord ↥A O.toricRank m)))).val :
            SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 ≫ pullback.fst Λ.f Λ.σA =
          Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫
            (O.degeneracyHom i).1 := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩

  haveI : IsProper Λ.f := hΛ.1.proper
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) := by
    show IsSeparated (pullback.snd Λ.f Λ.σA); infer_instance
  have hΛcomm : ∀ {T : Scheme.{0}} (t : T ⟶ base p) (x y : SchemeHomOver t Λ.f), Λ.L.mul t x y = Λ.L.mul t y x := hΛ.2.1

  let δA : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
    NeronSpecialFibreInfra.fibreRestrictAlong Λ.σA Λ.f O.g (O.degeneracyHom i)
  have δA_mul : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
      NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) δA =
        (Λ.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x δA) (NeronModelInfra.schemeHomOverComp y δA) := by
    intro T s x y
    apply (RelativeGroupLaw.baseChangePointEquiv Λ.σA s).injective
    show RelativeGroupLaw.baseChangePointToBase Λ.σA _ = RelativeGroupLaw.baseChangePointToBase Λ.σA _
    rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChangePointToBase_mul,
      O.degeneracyHom_mul i, RelativeGroupLaw.baseChangePointToBase_mul,
      RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong,
      RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong]

  let u : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
    NeronModelInfra.schemeHomOverComp (O.toricLift m hm) δA
  have hu1 : u.1 = (O.toricLift m hm).1 ≫ δA.1 := rfl
  have hufst : u.1 ≫ pullback.fst Λ.f Λ.σA = (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ (O.degeneracyHom i).1 := by
    rw [hu1, Category.assoc, NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst]

  let pt : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) →
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))))
        (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f) :=
    fun χ => NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u
  have hpt1 : ∀ χ, (pt χ).1 = Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1 := fun χ => rfl
  have hpt_mul : ∀ χ χ', pt (χ * χ') = (Λ.L.baseChange Λ.σA).mul _ (pt χ) (pt χ') := by
    intro χ χ'
    have h := congrArg (fun z => NeronModelInfra.schemeHomOverComp z δA) (O.toricLift_mul m hm χ χ')
    beta_reduce at h
    rw [δA_mul] at h

    have hassoc : ∀ θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) (O.toricLift m hm)) δA =
          pt (WithConv.toConv θ) := fun θ => Subtype.ext (Category.assoc _ _ _)
    rw [hassoc, hassoc, hassoc] at h
    exact h
  have hpt_one : pt 1 = (Λ.L.baseChange Λ.σA).one _ := by
    set a := pt 1 with ha
    have h2 : (Λ.L.baseChange Λ.σA).mul _ a a = a := by rw [ha, ← hpt_mul, mul_one]
    calc a = (Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).one _) a := ((Λ.L.baseChange Λ.σA).one_mul _ a).symm
      _ = (Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).inv _ a) a) a := by
          rw [(Λ.L.baseChange Λ.σA).inv_mul_cancel]
      _ = (Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).inv _ a) ((Λ.L.baseChange Λ.σA).mul _ a a) := by
          rw [(Λ.L.baseChange Λ.σA).mul_assoc]
      _ = (Λ.L.baseChange Λ.σA).one _ := by rw [h2, (Λ.L.baseChange Λ.σA).inv_mul_cancel]

  have hgl : ∀ (χ ψ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)) (g : Fin O.toricRank → ZMod m),
      (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro χ ψ g
    rw [AlgHom.convMul_def]
    simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]
  have hone_gl : ∀ g : Fin O.toricRank → ZMod m,
      (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv (AddMonoidAlgebra.single g 1) = 1 := by
    intro g
    rw [AlgHom.convOne_def]
    simp [AddMonoidAlgebra.counit_single]
  have htors : ∀ χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ), χ ^ m = 1 := by
    intro χ
    have hpow : ∀ (k : ℕ) (g : Fin O.toricRank → ZMod m),
        (χ ^ k).ofConv (AddMonoidAlgebra.single g 1) = (χ.ofConv (AddMonoidAlgebra.single g 1)) ^ k := by
      intro k g
      induction k with
      | zero => rw [pow_zero, pow_zero, hone_gl]
      | succ k ih => rw [pow_succ, hgl, ih, pow_succ]
    have hext : (χ ^ m).ofConv = (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv := by
      refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
      intro g
      rw [hpow, hone_gl, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
      have hmg : m • g = 0 := by
        funext j; simp
      rw [hmg]
      exact map_one χ.ofConv
    exact congrArg WithConv.toConv hext

  haveI : IsReduced (AddMonoidAlgebra (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m)) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero (AlgebraicClosure ℚ) _
  haveI : IsReduced (muCoord ↥A O.toricRank m) :=
    isReduced_of_injective (R := muCoord ↥A O.toricRank m)
      (S := AddMonoidAlgebra (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m))
      (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (algebraMap ↥A (AlgebraicClosure ℚ)))
      (AddMonoidAlgebra.map_injective (M := Fin O.toricRank → ZMod m)
        (algebraMap ↥A (AlgebraicClosure ℚ) : ↥A →+ AlgebraicClosure ℚ) Subtype.val_injective)
  haveI : IsReduced (Spec (CommRingCat.of (muCoord ↥A O.toricRank m))) := (affine_isReduced_iff _).mpr inferInstance
  haveI : Flat (muStr ↥A O.toricRank m) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap ↥A (muCoord ↥A O.toricRank m)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : LocallyOfFiniteType (muStr ↥A O.toricRank m) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    show (algebraMap ↥A (muCoord ↥A O.toricRank m)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance

  have hpt_eq : ∀ χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      (⟨Spec.map (CommRingCat.ofHom χ.ofConv.toRingHom) ≫ u.1, by
          rw [Category.assoc, u.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2; exact χ.ofConv.comp_algebraMap⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))))
          (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)) = pt χ := fun χ => Subtype.ext rfl
  have hutors : (Λ.L.baseChange Λ.σA).nsmul (muStr ↥A O.toricRank m) m u = (Λ.L.baseChange Λ.σA).one _ := by
    refine GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_one_of_forall_withConv_point (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) (Λ.L.baseChange Λ.σA) (muCoord ↥A O.toricRank m) u ?_ ?_ m htors
    · rw [hpt_eq]; exact hpt_one
    · intro χ χ'; rw [hpt_eq, hpt_eq, hpt_eq]; exact hpt_mul χ χ'
  have humem : u ∈ (Λ.L.baseChange Λ.σA).torsionSubset (muStr ↥A O.toricRank m) m :=
(RelativeGroupLaw.mem_torsionSubset _ _ _ _).mpr hutors
  let φ₀ : H →ₐ[↥A] muCoord ↥A O.toricRank m := ((e (muCoord ↥A O.toricRank m)).symm ⟨u, humem⟩).ofConv
  have hφ₀ : e (muCoord ↥A O.toricRank m) (WithConv.toConv φ₀) = ⟨u, humem⟩ := by
    show e _ (WithConv.toConv ((e (muCoord ↥A O.toricRank m)).symm ⟨u, humem⟩).ofConv) = _
    exact (e _).apply_symm_apply _

  have hθ : ∀ (T : Type) [CommRing T] [Algebra ↥A T] (θ : muCoord ↥A O.toricRank m →ₐ[↥A] T),
      ((e T (.toConv (θ.comp φ₀))).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)).1 =
        Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ u.1 := by
    intro T _ _ θ
    have h := he_nat (muCoord ↥A O.toricRank m) T θ (WithConv.toConv φ₀)
    rw [hφ₀] at h
    exact h
  have hθ' : ∀ χ : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      ((e _ (.toConv (χ.ofConv.comp φ₀))).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)) = pt χ :=
    fun χ => Subtype.ext ((hθ _ χ.ofConv).trans (hpt1 χ).symm)

  have he_one : ∀ (T : Type) [CommRing T] [Algebra ↥A T],
      ((e T 1).val : SchemeHomOver _ (RelativeGroupLaw.baseChangeStr Λ.σA Λ.f)) = (Λ.L.baseChange Λ.σA).one _ := by
    intro T _ _
    set a := (e T 1).val with ha
    have h2 : (Λ.L.baseChange Λ.σA).mul _ a a = a := by rw [ha, ← he_mul, mul_one]
    calc a = (Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).one _) a := ((Λ.L.baseChange Λ.σA).one_mul _ a).symm
      _ = (Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).inv _ a) a) a := by
          rw [(Λ.L.baseChange Λ.σA).inv_mul_cancel]
      _ = (Λ.L.baseChange Λ.σA).mul _ ((Λ.L.baseChange Λ.σA).inv _ a) ((Λ.L.baseChange Λ.σA).mul _ a a) := by
          rw [(Λ.L.baseChange Λ.σA).mul_assoc]
      _ = (Λ.L.baseChange Λ.σA).one _ := by rw [h2, (Λ.L.baseChange Λ.σA).inv_mul_cancel]

  haveI : IsReduced ((AlgebraicClosure ℚ) ⊗[↥A] (muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m)) :=
    aux_isReduced_baseChange_tensor_addMonoidAlgebra (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m)
  haveI : NoZeroSMulDivisors ↥A (muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m) :=
    aux_noZeroSMulDivisors_of_free _
  have hsep : ∀ x : muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m,
      (∀ θ : muCoord ↥A O.toricRank m ⊗[↥A] muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ, θ x = 0) → x = 0 :=
    fun x hx => Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct (AlgebraicClosure ℚ)
      (AlgebraicClosure ℚ) x hx
  have hinjA : Function.Injective (algebraMap ↥A (AlgebraicClosure ℚ)) := Subtype.val_injective
  have hone0 : (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv.comp φ₀ =
      (1 : WithConv (H →ₐ[↥A] AlgebraicClosure ℚ)).ofConv := by
    have h : e _ (.toConv ((1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv.comp φ₀)) = e _ 1 := by
      apply Subtype.ext
      rw [hθ' 1, hpt_one, he_one]
    exact congrArg WithConv.ofConv ((e _).injective h)
  have hmul0 : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      (χ * χ').ofConv.comp φ₀ =
        (WithConv.toConv (χ.ofConv.comp φ₀) * WithConv.toConv (χ'.ofConv.comp φ₀)).ofConv := by
    intro χ χ'
    have h : e _ (.toConv ((χ * χ').ofConv.comp φ₀)) =
        e _ (WithConv.toConv (χ.ofConv.comp φ₀) * WithConv.toConv (χ'.ofConv.comp φ₀)) := by
      apply Subtype.ext
      rw [hθ' (χ * χ'), he_mul, hθ' χ, hθ' χ', hpt_mul]
    exact congrArg WithConv.ofConv ((e _).injective h)
  obtain ⟨φ, hφ⟩ := BialgHom.exists_coe_eq_of_forall_withConv_comp hinjA φ₀ hsep hone0 hmul0

  refine ⟨φ, fun T _ _ ψ => ?_⟩
  rw [hφ, hθ T ψ, Category.assoc, hufst]

end S_ModularCurve_JZeroNeronObjectAtP_exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_bialgHom_muCoord_forall_torsionPoint_comp_fst_eq (solution)
