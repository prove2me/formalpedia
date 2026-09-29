-- Prove2me | solution 1 for ModularCurve.exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d951fd0e-2127-5b11-b344-565e16f41cbe

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open Polynomial IntermediateField ModularCurve
open scoped IntermediateField.algebraAdjoinAdjoin

namespace U0Dedekind

variable (K : Type*) [Field K] (N : ℕ)

local notation "LK" => LaurentSeries K
local notation "FN" => modularFunctionFieldFullC K N

def jF : FN := jModElt K (jqModC_mem_full K N)

@[scoped simp] theorem coe_jF : ((jF K N : FN) : LK) = jqModC K := rfl

local notation "Ej" => (IntermediateField.adjoin K ({jF K N} : Set (modularFunctionFieldFullC K N)))

local notation "Aj" => (Algebra.adjoin K ({jF K N} : Set (modularFunctionFieldFullC K N)))

local notation "E0" => (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))

theorem transcendental_jF : Transcendental K (jF K N) := by
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (modularFunctionFieldFullC K N) (LaurentSeries K))]
  exact ModularCurve.transcendental_jqModC K

theorem lift_Ej : lift Ej = E0 := lift_adjoin_simple K _ (jF K N)

theorem coe_mem_FN (z : E0) : (z : LK) ∈ FN :=
  lift_le Ej ((lift_Ej K N).symm ▸ z.2 : (z : LK) ∈ lift Ej)

theorem mk_mem_Ej (z : E0) : (⟨(z : LK), coe_mem_FN K N z⟩ : FN) ∈ Ej :=
  (mem_lift (⟨(z : LK), coe_mem_FN K N z⟩ : FN)).mp ((lift_Ej K N).symm ▸ z.2 : (z : LK) ∈ lift Ej)

def ψ : E0 →+* Ej where
  toFun z := ⟨⟨(z : LK), coe_mem_FN K N z⟩, mk_mem_Ej K N z⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_ψ (z : E0) : ((ψ K N z : Ej) : FN) = ⟨(z : LK), coe_mem_FN K N z⟩ := rfl

theorem coe_coe_ψ (z : E0) : (((ψ K N z : Ej) : FN) : LK) = (z : LK) :=
  congrArg Subtype.val (coe_ψ K N z)

theorem comp_ψ :
    ((algebraMap FN LK).comp (algebraMap Ej FN)).comp (ψ K N) = algebraMap E0 LK :=
  RingHom.ext fun z => coe_coe_ψ K N z

theorem isIntegral_of_coe (x : FN) (hx : IsIntegral E0 (x : LK)) : IsIntegral Ej x := by
  obtain ⟨p, hp, hp0⟩ := hx
  refine ⟨p.map (ψ K N), hp.map _, ?_⟩
  apply (algebraMap FN LK).injective
  rw [hom_eval₂, eval₂_map, comp_ψ, map_zero]
  exact hp0

theorem isSeparable_of_coe (x : FN) (hx : IsSeparable E0 (x : LK)) : IsSeparable Ej x := by
  have hμsep : ((minpoly E0 (x : LK)).map (ψ K N)).Separable := Polynomial.Separable.map hx
  have haevalL : algebraMap FN LK (aeval x ((minpoly E0 (x : LK)).map (ψ K N))) = 0 := by
    rw [aeval_def, hom_eval₂, eval₂_map, comp_ψ, ← aeval_def]
    exact minpoly.aeval E0 (x : LK)
  have haeval : aeval x ((minpoly E0 (x : LK)).map (ψ K N)) = 0 :=
    (algebraMap FN LK).injective (haevalL.trans (map_zero _).symm)
  exact hμsep.of_dvd (minpoly.dvd Ej x haeval)

def gens : Set FN := {x | (x : LK) ∈ divisorExpansionsC K N}

theorem adjoin_gens : (adjoin K (gens K N) : IntermediateField K FN) = ⊤ := by
  apply IntermediateField.lift_injective
  refine (lift_adjoin K _ (gens K N)).trans
    (Eq.trans ?_ (lift_top K (modularFunctionFieldFullC K N)).symm)
  apply le_antisymm
  · exact adjoin_le_iff.mpr (by rintro _ ⟨x, hx, rfl⟩; exact x.2)
  · show adjoin K (divisorExpansionsC K N) ≤ _
    refine adjoin.mono K _ _ fun y hy => ?_
    exact ⟨⟨y, subset_adjoin K _ hy⟩, hy, rfl⟩

theorem adjoin_Ej_gens : (adjoin Ej (gens K N) : IntermediateField Ej FN) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (adjoin K (gens K N) : IntermediateField K FN) := by
    rw [adjoin_gens]; exact mem_top
  have hle : (adjoin K (gens K N) : IntermediateField K FN) ≤
      restrictScalars K (adjoin Ej (gens K N)) := by
    rw [restrictScalars_adjoin]
    exact adjoin.mono K _ _ Set.subset_union_right
  exact hle hx

theorem gens_finite [NeZero N] : (gens K N).Finite := by
  classical
  let g : N.divisors → FN := fun d =>
    haveI : NeZero (d : ℕ) := ⟨Nat.pos_iff_ne_zero.mp (Nat.pos_of_mem_divisors d.2)⟩
    ⟨qExpand K d (jqModC K), jqModCd_mem_full K N (Nat.dvd_of_mem_divisors d.2)⟩
  refine (Set.finite_range g).subset ?_
  rintro ⟨x, hx⟩ ⟨d, hne, hd, rfl⟩
  refine ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩⟩, Subtype.ext ?_⟩
  exact qExpand_congr rfl _

theorem isIntegral_of_mem_gens {x : FN} (hx : x ∈ gens K N) : IsIntegral Ej x := by
  obtain ⟨d, hd, -, hxd⟩ := hx
  refine isIntegral_of_coe K N x ?_
  rw [hxd]
  exact ModularCurve.isIntegral_jqNModC_all K d

theorem isSeparable_of_mem_gens (hN : (N : K) ≠ 0) {x : FN} (hx : x ∈ gens K N) :
    IsSeparable Ej x := by
  obtain ⟨d, hd, hdvd, hxd⟩ := hx
  have hdK : (d : K) ≠ 0 := by
    obtain ⟨e, rfl⟩ := hdvd
    intro h; apply hN; rw [Nat.cast_mul, h, zero_mul]
  refine isSeparable_of_coe K N x ?_
  rw [hxd]
  exact ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero K d hdK

theorem finiteDimensional_Ej [NeZero N] : FiniteDimensional Ej FN := by
  haveI : Finite (gens K N) := (gens_finite K N).to_subtype
  haveI : FiniteDimensional Ej (adjoin Ej (gens K N)) :=
    finiteDimensional_adjoin fun y hy => isIntegral_of_mem_gens K N hy
  haveI : FiniteDimensional Ej (⊤ : IntermediateField Ej FN) := by
    rw [← adjoin_Ej_gens]; infer_instance
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv : (⊤ : IntermediateField Ej FN) ≃ₐ[Ej] FN).toLinearEquiv

theorem isSeparable_Ej (hN : (N : K) ≠ 0) : Algebra.IsSeparable Ej FN := by
  haveI : Algebra.IsSeparable Ej (adjoin Ej (gens K N) : IntermediateField Ej FN) :=
    (isSeparable_adjoin_iff_isSeparable _ _).mpr fun x hx => isSeparable_of_mem_gens K N hN hx
  haveI : Algebra.IsSeparable Ej (⊤ : IntermediateField Ej FN) := by
    rw [← adjoin_Ej_gens]; infer_instance
  exact AlgEquiv.Algebra.isSeparable
    (IntermediateField.topEquiv : (⊤ : IntermediateField Ej FN) ≃ₐ[Ej] FN)

def polyEquiv : K[X] ≃ₐ[K] Aj :=
  Polynomial.algEquivOfTranscendental K (jF K N) (transcendental_jF K N)

theorem algebraMap_polyEquiv (q : K[X]) :
    algebraMap Aj FN (polyEquiv K N q) = aeval (jF K N) q := by
  rw [polyEquiv, Polynomial.algEquivOfTranscendental_apply]
  show (Algebra.adjoin K ({jF K N} : Set FN)).val (aeval _ q) = aeval (jF K N) q
  rw [← aeval_algHom_apply]
  rfl

theorem algebraMap_comp_polyEquiv :
    (algebraMap Aj FN).comp (polyEquiv K N).toAlgHom.toRingHom = (aeval (jF K N)).toRingHom :=
  RingHom.ext fun q => algebraMap_polyEquiv K N q

theorem aeval_comp_polyEquiv_symm :
    (aeval (jF K N)).toRingHom.comp (polyEquiv K N).symm.toAlgHom.toRingHom = algebraMap Aj FN :=
  RingHom.ext fun a => by
    have h := algebraMap_polyEquiv K N ((polyEquiv K N).symm a)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm

theorem isPrincipalIdealRing_Aj : IsPrincipalIdealRing Aj :=
  IsPrincipalIdealRing.of_surjective (polyEquiv K N).toAlgHom.toRingHom (polyEquiv K N).surjective

theorem isIntegral_Aj_iff (a : FN) :
    IsIntegral Aj a ↔
      ∃ P : Polynomial (Polynomial K), P.Monic ∧
        Polynomial.eval₂ (Polynomial.aeval (R := K) (jF K N)).toRingHom a P = 0 := by
  constructor
  · rintro ⟨p, hp, hp0⟩
    refine ⟨p.map (polyEquiv K N).symm.toAlgHom.toRingHom, hp.map _, ?_⟩
    rw [eval₂_map, aeval_comp_polyEquiv_symm]
    exact hp0
  · rintro ⟨P, hP, hP0⟩
    refine ⟨P.map (polyEquiv K N).toAlgHom.toRingHom, hP.map _, ?_⟩
    rw [eval₂_map, algebraMap_comp_polyEquiv]
    exact hP0

theorem main [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ A : Subalgebra K FN,
      IsDedekindDomain A ∧ IsFractionRing A FN ∧
        ∀ a : FN, a ∈ A ↔
          (∃ P : Polynomial (Polynomial K), P.Monic ∧
            Polynomial.eval₂ (Polynomial.aeval (R := K) (jF K N)).toRingHom a P = 0) := by
  haveI : IsPrincipalIdealRing Aj := isPrincipalIdealRing_Aj K N
  haveI : IsDedekindDomain Aj := IsPrincipalIdealRing.isDedekindDomain _
  haveI : FiniteDimensional Ej FN := finiteDimensional_Ej K N
  haveI : Algebra.IsSeparable Ej FN := isSeparable_Ej K N hN
  have hD : IsDedekindDomain (integralClosure Aj FN) := integralClosure.isDedekindDomain Aj Ej FN
  have hF : IsFractionRing (integralClosure Aj FN) FN :=
    integralClosure.isFractionRing_of_finite_extension Ej FN
  refine ⟨(integralClosure Aj FN).restrictScalars K, hD, hF, fun a => ?_⟩
  rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact isIntegral_Aj_iff K N a

end U0Dedekind
p2m_reactivate "P2MW.S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt.U0Dedekind"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt.U0Dedekind"

universe u

theorem solution
    (K : Type u) [Field K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ∃ A : Subalgebra K ↥(ModularCurve.modularFunctionFieldFullC K N),
      IsDedekindDomain ↥A ∧ IsFractionRing ↥A ↥(ModularCurve.modularFunctionFieldFullC K N) ∧
        ∀ a : ↥(ModularCurve.modularFunctionFieldFullC K N), a ∈ A ↔ (∃ P : Polynomial (Polynomial K), P.Monic ∧ Polynomial.eval₂ (Polynomial.aeval (R := K) (ModularCurve.jModElt K (ModularCurve.jqModC_mem_full K N))).toRingHom a P = 0) :=
  U0Dedekind.main K N hN

end S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt
end P2MW
export P2MW.S_ModularCurve_exists_subalgebra_isDedekindDomain_isFractionRing_mem_iff_isIntegral_jModElt (solution)
