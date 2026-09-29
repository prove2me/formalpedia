-- Prove2me | solution 1 for MvFormalGroup.CartierModule.baseChange_surjective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9793875b-f2ea-5431-a75c-77f87634713f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebungInt_eq
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

open MvFormalGroup MvFormalGroup.CartierModule

universe u v

namespace P2mKcBaseChangeSurj

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ}

section OverS

variable {S : Type v} [CommRing S] [Algebra ℤ_[p] S] {Ψ : MvFormalGroup d S} [Ψ.IsComm]

omit [Algebra ℤ_[p] S] in

theorem tangent_sum_homothety_single (e : Fin d → CartierModule p Ψ)
    (he : ∀ i, tangent (e i) = Pi.single i 1) (c : Fin d → S) :
    tangent (∑ i : Fin d, homothety (c i) (e i)) = c := by
  rw [map_sum]
  funext j
  rw [Finset.sum_apply]
  simp only [tangent_homothety, he, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_step (e : Fin d → CartierModule p Ψ) (he : ∀ i, tangent (e i) = Pi.single i 1)
    (g : CartierModule p Ψ) :
    ∃ g₁ : CartierModule p Ψ,
      g = (∑ i : Fin d, homothety (tangent g i) (e i)) + verschiebungInt g₁ := by
  have htan : tangent (g - ∑ i : Fin d, homothety (tangent g i) (e i)) = 0 := by
    rw [map_sub, tangent_sum_homothety_single e he, sub_self]
  obtain ⟨g₁, hg₁⟩ :=
    (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebungInt_eq p Ψ _).mp htan
  exact ⟨g₁, by rw [hg₁, add_sub_cancel]⟩

def seq (e : Fin d → CartierModule p Ψ) (he : ∀ i, tangent (e i) = Pi.single i 1)
    (g : CartierModule p Ψ) : ℕ → CartierModule p Ψ
  | 0 => g
  | m + 1 => Classical.choose (exists_step e he (seq e he g m))

theorem seq_succ_spec (e : Fin d → CartierModule p Ψ) (he : ∀ i, tangent (e i) = Pi.single i 1)
    (g : CartierModule p Ψ) (m : ℕ) :
    seq e he g m = (∑ i : Fin d, homothety (tangent (seq e he g m) i) (e i)) +
      verschiebungInt (seq e he g (m + 1)) :=
  Classical.choose_spec (exists_step e he (seq e he g m))

theorem eq_sum_range (e : Fin d → CartierModule p Ψ) (he : ∀ i, tangent (e i) = Pi.single i 1)
    (g : CartierModule p Ψ) (N : ℕ) :
    g = (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m]
          (∑ i : Fin d, homothety (tangent (seq e he g m) i) (e i))) +
        (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] (seq e he g N) := by
  induction N with
  | zero => simp [seq]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, Function.iterate_succ_apply, ← iterate_map_add,
      ← seq_succ_spec]
    exact ih

end OverS

end P2mKcBaseChangeSurj

open P2mKcBaseChangeSurj in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {S : Type v} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.baseChange (p := p) (Φ := Φ) f :
        MvFormalGroup.CartierModule p Φ → MvFormalGroup.CartierModule p (Φ.map f)) := by
  classical
  intro g

  letI : Algebra ℤ_[p] S := (f.comp (algebraMap ℤ_[p] R)).toAlgebra

  have hsurj := MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt p Φ
  choose e he using fun i : Fin d => hsurj (Pi.single i 1)
  set e' : Fin d → CartierModule p (Φ.map f) := fun i => baseChange f (e i) with he'_def
  have he' : ∀ i, tangent (e' i) = Pi.single i 1 := by
    intro i
    rw [he'_def, tangent_baseChangeEq, he i]
    funext j
    rw [Pi.single_apply, Pi.single_apply, apply_ite f, map_one, map_zero]

  set c : ℕ → Fin d → S := fun m => tangent (seq e' he' g m) with hc
  set ct : ℕ → Fin d → R := fun m i => Function.surjInv hf (c m i) with hct
  have hfct : ∀ m i, f (ct m i) = c m i := fun m i => Function.surjInv_eq hf (c m i)
  set x : ℕ → CartierModule p Φ := fun m => ∑ i : Fin d, homothety (ct m i) (e i) with hx
  have hbx : ∀ m, baseChange f (x m) = ∑ i : Fin d, homothety (c m i) (e' i) := by
    intro m
    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [baseChangeEq_homothety, hfct]

  obtain ⟨s, hs, -⟩ :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Φ x
  refine ⟨s, ?_⟩

  have huniq :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p
      (Φ.map f) (fun m => ∑ i : Fin d, homothety (c m i) (e' i))
  refine huniq.unique ?_ ?_
  · intro N
    obtain ⟨t, ht⟩ := hs N
    refine ⟨baseChange f t, ?_⟩
    rw [ht, map_add, map_sum, baseChangeEq_verschiebungInt_iterate]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [baseChangeEq_verschiebungInt_iterate, hbx]
  · intro N
    exact ⟨seq e' he' g N, eq_sum_range e' he' g N⟩

end
end S_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_baseChange_surjective_of_surjective (solution)
