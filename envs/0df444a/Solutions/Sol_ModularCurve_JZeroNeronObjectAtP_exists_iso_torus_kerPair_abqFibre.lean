-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_iso_torus_kerPair_abqFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3f3ff986-0279-5da9-8132-9893430ad007

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair

import Theorems.Thm_AlgebraicGeometry_ext_of_forall_geometricPoint_comp_eq_of_flat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_torus_kerPair_abqFibre

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

end Generic

section Fibre

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A} (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

noncomputable abbrev Lκ : RelativeGroupLaw (ResidueField ↥A) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  O.L.baseChange (resPt A ≫ Λ.σA)

noncomputable abbrev K : Scheme.{0} := RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre

noncomputable abbrev KStr : K O ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := RelativeGroupLaw.kerPairStr (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre

noncomputable abbrev LK : RelativeGroupLaw (ResidueField ↥A) (KStr O) :=
  RelativeGroupLaw.kerPairLaw (Lκ O) (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)

noncomputable abbrev eqv {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) :=
  RelativeGroupLaw.kerPairPointEquiv (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre t

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

theorem tpt_pow (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) (n : ℕ) :
    (Lκ O).nsmul (𝟙 _) n (tpt O χ) = tpt O (χ ^ n) := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero, tpt_one]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, tpt_mul]

theorem torusFibre_mem (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp O.torusFibre (O.abqFibre i) = (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (torusStr (ResidueField ↥A) O.toricRank) :=
  (O.abqFibre_eq_one_iff (torusStr (ResidueField ↥A) O.toricRank) O.torusFibre).mpr
    ⟨⟨𝟙 _, Category.id_comp _⟩, Subtype.ext (Category.id_comp _)⟩ i

noncomputable def jOver : SchemeHomOver (torusStr (ResidueField ↥A) O.toricRank) (KStr O) :=
  (eqv O (torusStr (ResidueField ↥A) O.toricRank)).symm ⟨O.torusFibre, torusFibre_mem O⟩

theorem j_comp_kerPairι : (jOver O).1 ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre = O.torusFibre.1 :=
  RelativeGroupLaw.kerPairPointEquiv_symm_apply_coe _ _ _ _

theorem j_over : (jOver O).1 ≫ KStr O = torusStr (ResidueField ↥A) O.toricRank := (jOver O).2

theorem eqv_torusPoint (τ : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank)) :
    (eqv O (𝟙 _) ⟨τ.1 ≫ (jOver O).1, by rw [Category.assoc, j_over, τ.2]⟩).1 =
      NeronModelInfra.schemeHomOverComp τ O.torusFibre := by
  apply Subtype.ext
  rw [RelativeGroupLaw.kerPairPointEquiv_apply_coe_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    j_comp_kerPairι]

theorem eq_of_eqv_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))}
    {z w : SchemeHomOver t (KStr O)} (h : (eqv O t z).1 = (eqv O t w).1) : z = w :=
  (eqv O t).injective (Subtype.ext h)

theorem eqv_nsmul_torusPt (χ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A))
    (n : ℕ) :
    (eqv O (𝟙 _) ((LK O).nsmul (𝟙 _) n
        ⟨(torusPt _ _ χ.ofConv).1 ≫ (jOver O).1, by rw [Category.assoc, j_over, (torusPt _ _ χ.ofConv).2]⟩)).1 =
      tpt O (χ ^ n) := by
  rw [RelativeGroupLaw.kerPairPointEquiv_nsmul, eqv_torusPoint, tpt_pow]

theorem kerPairιOver_mem (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.kerPairιOver (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre) (O.abqFibre i) =
      (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (KStr O) := by
  have h := RelativeGroupLaw.kerPairι_mem (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (⟨𝟙 (K O), Category.id_comp _⟩ : SchemeHomOver (KStr O) (KStr O)) i
  have e : (⟨𝟙 (K O) ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre, by rw [Category.assoc]; exact Category.id_comp _⟩ :
      SchemeHomOver (KStr O) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)) =
      RelativeGroupLaw.kerPairιOver (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre := Subtype.ext (Category.id_comp _)
  rw [e] at h
  exact h

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
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_torus_kerPair_abqFibre.LBA"

open LBA in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    ∃ e : torusScheme (ResidueField ↥A) O.toricRank ≅
        RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre,
      e.hom ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre = O.torusFibre.1 ∧
      ∀ n : ℕ, e.hom ≫ (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA))
          (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫
          e.hom := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := O.locallyOfFiniteType
  haveI := O.quasiCompact
  haveI := O.separated
  haveI : IsSeparated Λ.f := hΛ.1.proper.toIsSeparated
  haveI := O.torusFibre_isClosedImmersion

  obtain ⟨y, hy⟩ := (O.abqFibre_eq_one_iff (KStr O) (RelativeGroupLaw.kerPairιOver (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre)).mp
    (kerPairιOver_mem O)
  have hy1 : y.1 ≫ O.torusFibre.1 = RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre := congrArg Subtype.val hy
  let j : torusScheme (ResidueField ↥A) O.toricRank ⟶ K O := (jOver O).1
  have hjι : j ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre = O.torusFibre.1 := j_comp_kerPairι O
  have hjf : j ≫ KStr O = torusStr (ResidueField ↥A) O.toricRank := j_over O
  let e : torusScheme (ResidueField ↥A) O.toricRank ≅ K O :=
    { hom := j
      inv := y.1
      hom_inv_id := by
        rw [← cancel_mono O.torusFibre.1, Category.assoc, hy1, hjι, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre), Category.assoc, hjι, hy1, Category.id_comp] }
  refine ⟨e, hjι, fun n => ?_⟩
  show j ≫ (LK O).schemeNsmul n = _ ≫ j
  haveI : LocallyOfFinitePresentation (torusStr (ResidueField ↥A) O.toricRank) := inferInstance
  refine AlgebraicGeometry.ext_of_forall_geometricPoint_comp_eq_of_flat (RingHom.id (ResidueField ↥A))
    Function.injective_id (torusStr (ResidueField ↥A) O.toricRank) (KStr O) ?_ ?_ ?_
  · rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over, hjf]
  · rw [Category.assoc, hjf, nT_over]
  intro x hx
  have hx' : x ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ := by
    rw [hx]; change Spec.map (𝟙 _) = _; exact Spec.map_id _
  obtain ⟨χ, hχ⟩ := exists_torusPt_eq _ _ ⟨x, hx'⟩
  have hxχ : x = (torusPt _ _ χ).1 := (congrArg Subtype.val hχ).symm
  let w : SchemeHomOver (𝟙 _) (KStr O) :=
    ⟨(torusPt _ _ χ).1 ≫ j, by rw [Category.assoc, hjf, (torusPt _ _ χ).2]⟩
  have hl : x ≫ j ≫ (LK O).schemeNsmul n = ((LK O).nsmul (𝟙 _) n w).1 := by
    rw [← Category.assoc, hxχ]
    exact comp_schemeNsmul (LK O) n w
  let w' : SchemeHomOver (𝟙 _) (KStr O) :=
    ⟨(torusPt _ _ (WithConv.toConv χ ^ n).ofConv).1 ≫ j, by
      rw [Category.assoc, hjf, (torusPt _ _ (WithConv.toConv χ ^ n).ofConv).2]⟩
  have hr : x ≫ Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ j = w'.1 := by
    show _ = (torusPt _ _ (WithConv.toConv χ ^ n).ofConv).1 ≫ j
    rw [torusPt_pow_coe, hxχ, Category.assoc]
  rw [hl, hr]
  congr 1
  apply eq_of_eqv_eq O
  rw [eqv_nsmul_torusPt O (WithConv.toConv χ) n, eqv_torusPoint]

end S_ModularCurve_JZeroNeronObjectAtP_exists_iso_torus_kerPair_abqFibre
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_iso_torus_kerPair_abqFibre (solution)
