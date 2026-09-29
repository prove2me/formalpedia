-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e0113f9f-240f-5a10-b583-0c130aaa43d8

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

import Theorems.Thm_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
import Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index
import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

namespace LBA

section TorusPoints

variable (S : Type) [CommRing S] (t : ℕ)

theorem exists_torusPt_eq (τ : SchemeHomOver (𝟙 _) (torusStr S t)) :
    ∃ χ : torusCoord S t →ₐ[S] S, torusPt S t χ = τ := by
  let ψ : CommRingCat.of (torusCoord S t) ⟶ CommRingCat.of S := Spec.preimage τ.1
  have hψ : Spec.map ψ = τ.1 := Spec.map_preimage _
  have hcomp : (CommRingCat.ofHom (algebraMap S (torusCoord S t))) ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hψ]
    exact τ.2
  refine ⟨{ ψ.hom with commutes' := fun r => ?_ }, ?_⟩
  · have := congrArg (fun g : CommRingCat.of S ⟶ CommRingCat.of S => g.hom r) hcomp
    simpa using this
  · apply Subtype.ext
    show Spec.map _ = τ.1
    rw [← hψ]
    rfl

variable {S t}

theorem convMul_single (χ χ' : WithConv (torusCoord S t →ₐ[S] S)) (v : Fin t → ℤ) :
    (χ * χ') (AddMonoidAlgebra.single v 1) = χ (AddMonoidAlgebra.single v 1) * χ' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single]
  simp [Algebra.TensorProduct.lift_tmul]

theorem convOne_single (v : Fin t → ℤ) :
    (1 : WithConv (torusCoord S t →ₐ[S] S)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single]
  simp

theorem convPow_single (χ : WithConv (torusCoord S t →ₐ[S] S)) (n : ℕ) (v : Fin t → ℤ) :
    (χ ^ n) (AddMonoidAlgebra.single v 1) = χ (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_single, ih]

theorem convPow_ofConv_toRingHom (χ : WithConv (torusCoord S t →ₐ[S] S)) (n : ℕ) :
    (χ ^ n).ofConv.toRingHom =
      χ.ofConv.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin t → ℤ))) := by
  have h : (χ ^ n).ofConv =
      χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S (n • AddMonoidHom.id (Fin t → ℤ))) := by
    refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro v
    rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    show (χ ^ n) (AddMonoidAlgebra.single v 1) = χ.ofConv (AddMonoidAlgebra.single ((n • AddMonoidHom.id _) v) 1)
    rw [convPow_single, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, ← one_pow n,
      ← AddMonoidAlgebra.single_pow, one_pow, map_pow]
  exact congrArg AlgHom.toRingHom h

theorem torusPt_pow_coe (χ : WithConv (torusCoord S t →ₐ[S] S)) (n : ℕ) :
    (torusPt S t (χ ^ n).ofConv).1 =
      (torusPt S t χ.ofConv).1 ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin t → ℤ)))) := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← convPow_ofConv_toRingHom]

noncomputable def convInv (χ : WithConv (torusCoord S t →ₐ[S] S)) : WithConv (torusCoord S t →ₐ[S] S) :=
  WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S (-AddMonoidHom.id (Fin t → ℤ))))

theorem convMul_convInv (χ : WithConv (torusCoord S t →ₐ[S] S)) : χ * convInv χ = 1 := by
  apply WithConv.ofConv_injective
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro v
  show (χ * convInv χ) (AddMonoidAlgebra.single v 1) = (1 : WithConv (torusCoord S t →ₐ[S] S)) (AddMonoidAlgebra.single v 1)
  rw [convMul_single, convOne_single]
  show χ (AddMonoidAlgebra.single v 1) *
      χ.ofConv (AddMonoidAlgebra.mapDomainAlgHom S S (-AddMonoidHom.id (Fin t → ℤ)) (AddMonoidAlgebra.single v 1)) = 1
  rw [AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  show χ.ofConv (AddMonoidAlgebra.single v 1) * χ.ofConv (AddMonoidAlgebra.single (-v) 1) = 1
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
  exact map_one χ.ofConv

end TorusPoints

end LBA

namespace LBA

section Generic

universe v

variable {R : Type v} [CommRing R] {X : Scheme.{v}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem comp_schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{v}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) : x.1 ≫ G.schemeNsmul n = (G.nsmul t n x).1 := by
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint : SchemeHomOver f f) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  exact (congrArg Subtype.val h)

theorem one_coe_idComp (G : RelativeGroupLaw R f) {T : Scheme.{v}} (c : T ⟶ Spec (CommRingCat.of R)) :
    (G.one (𝟙 T ≫ c)).1 = (G.one c).1 := by
  have h := G.one_natural c (𝟙 T ≫ c) (𝟙 T) rfl
  rw [← h, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

end Generic

section Fibre

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A} (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

noncomputable abbrev Lκ : RelativeGroupLaw (ResidueField ↥A) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  O.L.baseChange (resPt A ≫ Λ.σA)

noncomputable abbrev dκ (i : Fin 2) :
    SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)
      (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) :=
  NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)

theorem dκ_isHom (i : Fin 2) : RelativeGroupLaw.IsHom (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O i) :=
  RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA) (fun t x y => O.degeneracyHom_mul i t x y)

noncomputable abbrev Hκ : Scheme.{0} := RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

noncomputable abbrev HκStr : Hκ O ⟶ Spec (CommRingCat.of (ResidueField ↥A)) :=
  RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

noncomputable abbrev LH : RelativeGroupLaw (ResidueField ↥A) (HκStr O) :=
  RelativeGroupLaw.kerPairLaw (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) (dκ_isHom O)

noncomputable abbrev eqv {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) :=
  RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) t

noncomputable abbrev tpt (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) O.torusFibre

theorem tpt_mul (χ χ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    tpt O (χ * χ') = (Lκ O).mul (𝟙 _) (tpt O χ) (tpt O χ') :=
  O.torusFibre_mul χ χ'

theorem tpt_one : tpt O 1 = (Lκ O).one (𝟙 _) := by
  letI := (Lκ O).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  have h := tpt_mul O 1 1
  rw [one_mul] at h
  exact mul_eq_left.mp h.symm

theorem tpt_inv (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    (Lκ O).inv (𝟙 _) (tpt O χ) = tpt O (convInv χ) := by
  letI := (Lκ O).pointGroup (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  have h : tpt O χ * tpt O (convInv χ) = 1 := by
    show (Lκ O).mul _ _ _ = (Lκ O).one _
    rw [← tpt_mul, convMul_convInv, tpt_one]
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem tpt_pow (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) (n : ℕ) :
    (Lκ O).nsmul (𝟙 _) n (tpt O χ) = tpt O (χ ^ n) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero, tpt_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, tpt_mul]

variable (hι : ∀ i : Fin 2, O.torusFibre.1 ≫
    (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)).1 =
  torusStr (ResidueField ↥A) O.toricRank ≫ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1)

include hι in
theorem torusFibre_mem (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp O.torusFibre (dκ O i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (torusStr (ResidueField ↥A) O.toricRank) := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.one_coe_eq]
  exact hι i

noncomputable def ιHOver : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (HκStr O) :=
  (eqv O (torusStr (ResidueField ↥A) O.toricRank)).symm ⟨O.torusFibre, torusFibre_mem O hι⟩

theorem ιH_comp_kerPairι :
    (ιHOver O hι).1 ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O) = O.torusFibre.1 :=
  RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe _ _ _ _

theorem ιH_over : (ιHOver O hι).1 ≫ HκStr O = torusStr (ResidueField ↥A) O.toricRank :=
  (ιHOver O hι).2

theorem eqv_torusPoint (τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    (eqv O (𝟙 _) ⟨τ.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ.2]⟩).1 =
      NeronModelInfra.schemeHomOverComp τ O.torusFibre := by
  apply Subtype.ext
  rw [RelativeGroupLaw.kerPairPointEquiv_apply_coe_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    ιH_comp_kerPairι]

theorem eq_of_eqv_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))}
    {z w : SchemeHomOver t (HκStr O)} (h : (eqv O t z).1 = (eqv O t w).1) : z = w :=
  (eqv O t).injective (Subtype.ext h)

theorem hmul (τ τ' : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    ∃ τ'' : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      (LH O).mul (𝟙 _) ⟨τ.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ.2]⟩
          ⟨τ'.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ'.2]⟩ =
        ⟨τ''.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ''.2]⟩ := by
  obtain ⟨χ, rfl⟩ := exists_torusPt_eq _ _ τ
  obtain ⟨χ', rfl⟩ := exists_torusPt_eq _ _ τ'
  refine ⟨torusPt _ _ (WithConv.toConv χ * WithConv.toConv χ').ofConv, ?_⟩
  apply eq_of_eqv_eq O
  rw [RelativeGroupLaw.kerPairPointEquiv_mul, eqv_torusPoint, eqv_torusPoint, eqv_torusPoint]
  exact (tpt_mul O (WithConv.toConv χ) (WithConv.toConv χ')).symm

theorem hinv (τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    ∃ τ' : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
      (LH O).inv (𝟙 _) ⟨τ.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ.2]⟩ =
        ⟨τ'.1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, τ'.2]⟩ := by
  obtain ⟨χ, rfl⟩ := exists_torusPt_eq _ _ τ
  refine ⟨torusPt _ _ (convInv (WithConv.toConv χ)).ofConv, ?_⟩
  apply eq_of_eqv_eq O
  rw [RelativeGroupLaw.kerPairPointEquiv_inv, eqv_torusPoint, eqv_torusPoint]
  exact tpt_inv O (WithConv.toConv χ)

theorem eqv_nsmul_torusPt (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A))
    (n : ℕ) :
    (eqv O (𝟙 _) ((LH O).nsmul (𝟙 _) n
        ⟨(torusPt _ _ χ.ofConv).1 ≫ (ιHOver O hι).1, by rw [Category.assoc, ιH_over, (torusPt _ _ χ.ofConv).2]⟩)).1 =
      tpt O (χ ^ n) := by
  rw [RelativeGroupLaw.kerPairPointEquiv_nsmul, eqv_torusPoint, tpt_pow]

scoped instance : IsReduced (Hκ O) := O.ker_degeneracyHom_special_isReduced

theorem hcomm : (LH O).IsCommutative :=
  RelativeGroupLaw.IsCommutative.kerPairLaw _ _ _ _ (RelativeGroupLaw.IsCommutative.baseChange (resPt A ≫ Λ.σA) O.comm)

scoped instance torus_locallyOfFiniteType (S : Type) [Field S] (t : ℕ) : LocallyOfFiniteType (torusStr S t) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

scoped instance torus_isReduced (S : Type) [Field S] (t : ℕ) : IsReduced (torusScheme S t) := by
  infer_instance

theorem nT_over (S : Type) [CommRing S] (t n : ℕ) :
    Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin t → ℤ)))) ≫
      torusStr S t = torusStr S t := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (AddMonoidAlgebra.mapDomainAlgHom S S (n • AddMonoidHom.id (Fin t → ℤ))).comp_algebraMap

end Fibre

end LBA
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le.LBA"

open LBA in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (hι : ∀ i : Fin 2, O.torusFibre.1 ≫
        (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)).1 =
      torusStr (ResidueField ↥A) O.toricRank ≫ ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1)
    (S : Finset (SchemeHomOver (resPt A ≫ Λ.σA) O.g))
    (hSK : ∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp s (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA))
    (hS : ∀ x : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
        (∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA)) →
        ∃ s ∈ S, ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
          toFibrePt x = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _)
            (NeronModelInfra.schemeHomOverComp τ O.torusFibre) (toFibrePt s))
    (m : ℕ) (hm : 0 < m) :
    letI LH := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA))
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i))
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA)
        (fun t x y => O.degeneracyHom_mul i t x y))
    IsFinite (LH.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (LH.schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ(LH.schemeKer m, ⊤) ≤ S.card * m ^ O.toricRank) := by
  classical

  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := O.locallyOfFiniteType
  haveI := O.quasiCompact
  haveI := O.separated
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  haveI := O.torusFibre_isClosedImmersion

  let ι : torusScheme (ResidueField ↥A) O.toricRank ⟶ Hκ O := (ιHOver O hι).1
  have hιf : ι ≫ HκStr O = torusStr (ResidueField ↥A) O.toricRank := ιH_over O hι
  haveI : IsClosedImmersion ι := by
    have : IsClosedImmersion (ι ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)) := by
      rw [ιH_comp_kerPairι]; infer_instance
    exact .of_comp ι (RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O))

  have hSK' : ∀ s ∈ S, ∀ i, NeronModelInfra.schemeHomOverComp (toFibrePt s) (dκ O i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    intro s hs i
    apply (RelativeGroupLaw.baseChangePointEquiv (resPt A ≫ Λ.σA) (f := Λ.f) (𝟙 _)).injective
    show RelativeGroupLaw.baseChangePointToBase _ _ = RelativeGroupLaw.baseChangePointToBase _ _
    rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, RelativeGroupLaw.baseChange_one,
      RelativeGroupLaw.baseChangePointToBase_ofBase]
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_idComp]
    show (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) (toFibrePt s)).1 ≫ _ = _
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact congrArg Subtype.val (hSK s hs i)
  let rep : {s // s ∈ S} → SchemeHomOver (𝟙 _) (HκStr O) := fun s =>
    (eqv O (𝟙 _)).symm ⟨toFibrePt s.1, hSK' s.1 s.2⟩
  have rep_eqv : ∀ s : {s // s ∈ S}, (eqv O (𝟙 _) (rep s)).1 = toFibrePt s.1 := fun s => by
    simp only [rep, Equiv.apply_symm_apply]
  let S' : Finset (SchemeHomOver (𝟙 _) (HκStr O)) := S.attach.image rep
  have hS'card : S'.card ≤ S.card := Finset.card_image_le.trans (by rw [Finset.card_attach])

  have hidx : ∀ x : SchemeHomOver (𝟙 _) (HκStr O), ∃ s ∈ S',
      ∃ τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
        x = (LH O).mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ := by
    intro z
    let uz := (eqv O (𝟙 _) z).1
    let x : SchemeHomOver (resPt A ≫ Λ.σA) O.g :=
      ⟨(RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz).1, by
        simpa only [Category.id_comp] using (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz).2⟩
    have hxu : overId x = RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz := Subtype.ext rfl
    have htx : toFibrePt x = uz := by
      rw [toFibrePt, hxu, RelativeGroupLaw.baseChangePointOfBase_toBase]
    have hx : ∀ i, NeronModelInfra.schemeHomOverComp x (O.degeneracyHom i) = Λ.L.one (resPt A ≫ Λ.σA) := by
      intro i
      have hR : RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA)
          ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)) = Λ.L.one (𝟙 _ ≫ (resPt A ≫ Λ.σA)) := by
        rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointToBase_ofBase]
      have h := congrArg (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA)) ((eqv O (𝟙 _) z).2 i)
      rw [RelativeGroupLaw.baseChangePointToBase_comp_fibreRestrictAlong, hR] at h
      change NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) uz)
        (O.degeneracyHom i) = _ at h
      rw [← hxu] at h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_idComp] at h'
      exact h'
    obtain ⟨s, hs, τ, hsτ⟩ := hS x hx
    refine ⟨rep ⟨s, hs⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), τ, ?_⟩
    apply eq_of_eqv_eq O
    rw [RelativeGroupLaw.kerPairPointEquiv_mul, rep_eqv, eqv_torusPoint]
    show uz = _
    rw [← htx, hsτ]
    exact RelativeGroupLaw.IsCommutative.mul_comm
      (RelativeGroupLaw.IsCommutative.baseChange (resPt A ≫ Λ.σA) O.comm) _ _ _

  haveI : IsOpenImmersion ι :=
    AlgebraicGeometry.isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index (HκStr O) (LH O)
      (torusStr (ResidueField ↥A) O.toricRank) ι hιf (hmul O hι) (hinv O hι) S' hidx

  have hιn : ∀ n : ℕ, ι ≫ (LH O).schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι := by
    intro n
    haveI : LocallyOfFinitePresentation (torusStr (ResidueField ↥A) O.toricRank) := inferInstance
    refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (RingHom.id (ResidueField ↥A))
      Function.injective_id (torusStr (ResidueField ↥A) O.toricRank) (HκStr O) ?_ ?_ ?_
    · rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over, hιf]
    · rw [Category.assoc, hιf, nT_over]
    intro y hy
    have hy' : y ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ := by
      rw [hy]; change Spec.map (𝟙 _) = _; exact Spec.map_id _
    obtain ⟨χ, hχ⟩ := exists_torusPt_eq _ _ ⟨y, hy'⟩
    have hyχ : y = (torusPt _ _ χ).1 := (congrArg Subtype.val hχ).symm

    let w : SchemeHomOver (𝟙 _) (HκStr O) :=
      ⟨(torusPt _ _ χ).1 ≫ ι, by rw [Category.assoc, hιf, (torusPt _ _ χ).2]⟩
    have hl : y ≫ ι ≫ (LH O).schemeNsmul n = ((LH O).nsmul (𝟙 _) n w).1 := by
      rw [← Category.assoc, hyχ]
      exact comp_schemeNsmul (LH O) n w
    let w' : SchemeHomOver (𝟙 _) (HκStr O) :=
      ⟨(torusPt _ _ (WithConv.toConv χ ^ n).ofConv).1 ≫ ι, by
        rw [Category.assoc, hιf, (torusPt _ _ (WithConv.toConv χ ^ n).ofConv).2]⟩
    have hr : y ≫ Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι = w'.1 := by
      show _ = (torusPt _ _ (WithConv.toConv χ ^ n).ofConv).1 ≫ ι
      rw [torusPt_pow_coe, hyχ, Category.assoc]
    rw [hl, hr]
    congr 1
    apply eq_of_eqv_eq O
    rw [eqv_nsmul_torusPt O hι (WithConv.toConv χ) n, eqv_torusPoint]

  obtain ⟨hfin, hrank⟩ :=
    AlgebraicGeometry.isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus (HκStr O) (LH O) (hcomm O)
      O.toricRank ι hιf hιn S' hidx m hm
  exact ⟨hfin, hrank.trans (Nat.mul_le_mul_right _ hS'card)⟩

end S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le (solution)
