-- Prove2me | solution 1 for MvFormalGroup.free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6ab44688-b73b-5d80-9e4c-1a7888baa592

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow
import Theorems.Thm_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open MvPowerSeries

universe u v

namespace LVb

open MvPowerSeries

section Comp

variable {𝓞 : Type u} [CommRing 𝓞] {E : Type v} [CommRing E] [Algebra 𝓞 E]
  {ι : Type*} [Fintype ι] (ε : Module.Basis ι 𝓞 E) {σ : Type*}

private noncomputable def comp (l : ι) (F : MvPowerSeries σ E) : MvPowerSeries σ 𝓞 := fun α => ε.repr (coeff α F) l

omit [Fintype ι] in
private theorem coeff_comp (l : ι) (F : MvPowerSeries σ E) (α : σ →₀ ℕ) : coeff α (comp ε l F) = ε.repr (coeff α F) l := rfl

private theorem coeff_sum_C_mul_map (G : ι → MvPowerSeries σ 𝓞) (α : σ →₀ ℕ) :
    coeff α (∑ l, C (ε l) * (G l).map (algebraMap 𝓞 E)) = ∑ l, coeff α (G l) • ε l := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_C_mul, coeff_map, Algebra.smul_def, mul_comm]

private theorem eq_sum_C_mul_map_comp (F : MvPowerSeries σ E) : F = ∑ l, C (ε l) * (comp ε l F).map (algebraMap 𝓞 E) := by
  ext α
  rw [coeff_sum_C_mul_map]
  simp only [coeff_comp]
  exact (ε.sum_repr (coeff α F)).symm

private theorem eq_comp_of_eq_sum (F : MvPowerSeries σ E) (G : ι → MvPowerSeries σ 𝓞)
    (h : F = ∑ l, C (ε l) * (G l).map (algebraMap 𝓞 E)) (l : ι) : G l = comp ε l F := by
  ext α
  rw [coeff_comp, h, coeff_sum_C_mul_map]
  have hli := ε.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have h0 : ∑ l', (coeff α (G l') - ε.repr (∑ l'', coeff α (G l'') • ε l'') l') • ε l' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, sub_eq_zero]
    exact (ε.sum_repr _).symm
  exact sub_eq_zero.mp (hli _ h0 l)

private theorem eq_zero_of_sum_eq_zero (G : ι → MvPowerSeries σ 𝓞) (h : ∑ l, C (ε l) * (G l).map (algebraMap 𝓞 E) = 0) (l : ι) :
    G l = 0 := by
  rw [eq_comp_of_eq_sum ε 0 G h.symm l]
  ext α
  rw [coeff_comp, coeff_zero, map_zero, Finsupp.zero_apply, coeff_zero]

end Comp

end LVb

namespace LVb

open MvPowerSeries

private theorem stepA
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)
    (hh : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ h)
    (E : Type v) [CommRing E] [Algebra 𝓞 E] [Module.Free 𝓞 E] [Module.Finite 𝓞 E] (v : ℕ) :
    ∃ e : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) E,
      ∀ F : MvPowerSeries (Fin d) E, ∃! c : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) E,
        F = ∑ j, MvPowerSeries.subst (fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E)) (c j) * e j := by
  classical
  obtain ⟨e₀, he₀⟩ :=
    MvFormalGroup.exists_forall_existsUnique_eq_sum_subst_nthSeries_mul_of_finrank_eq_pow p hp Φ h hh v

  let g₀ : Fin d → MvPowerSeries (Fin d) 𝓞 := Φ.nthSeries (p ^ v)
  let g : Fin d → MvPowerSeries (Fin d) E := fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E)
  have hg₀0 : ∀ i, constantCoeff (g₀ i) = 0 := MvFormalGroup.constantCoeff_nthSeries Φ _
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i => by
    show constantCoeff ((g₀ i).map (algebraMap 𝓞 E)) = 0
    rw [constantCoeff_map, hg₀0, map_zero]
  have hsg₀ := hasSubst_of_constantCoeff_zero hg₀0
  have hsg := hasSubst_of_constantCoeff_zero hg0
  have hms : ∀ G : MvPowerSeries (Fin d) 𝓞, (subst g₀ G).map (algebraMap 𝓞 E) = subst g (G.map (algebraMap 𝓞 E)) := fun G => map_subst hsg₀ G
  have hsC : ∀ (x : E) (c : MvPowerSeries (Fin d) E), subst g (C x * c) = C x * subst g c := fun x c => by
    rw [← coe_substAlgHom hsg, map_mul]
    congr 1
    rw [c_eq_algebraMap, AlgHom.commutes]
  have hsadd : ∀ c c' : MvPowerSeries (Fin d) E, subst g (c + c') = subst g c + subst g c' := fun c c' => by
    rw [← coe_substAlgHom hsg, map_add]
  have hssum : ∀ (c : Module.Free.ChooseBasisIndex 𝓞 E → MvPowerSeries (Fin d) E),
      subst g (∑ k, c k) = ∑ k, subst g (c k) := fun c => by
    rw [← coe_substAlgHom hsg, map_sum]

  let ε := Module.Free.chooseBasis 𝓞 E

  refine ⟨fun j => (e₀ j).map (algebraMap 𝓞 E), fun F => ?_⟩

  choose c₀ hc₀ using fun l => (he₀ (comp ε l F)).exists
  have hc₀u : ∀ l (c' : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) 𝓞),
      comp ε l F = ∑ j, subst g₀ (c' j) * e₀ j → c' = c₀ l := fun l c' hc' => (he₀ (comp ε l F)).unique hc' (hc₀ l)

  have hkey : ∀ c' : (Module.Free.ChooseBasisIndex 𝓞 E) → Fin (p ^ (v * h)) → MvPowerSeries (Fin d) 𝓞,
      ∑ j, subst g (∑ l, C (ε l) * (c' l j).map (algebraMap 𝓞 E)) * (e₀ j).map (algebraMap 𝓞 E) =
        ∑ l, C (ε l) * (∑ j, subst g₀ (c' l j) * e₀ j).map (algebraMap 𝓞 E) := by
    intro c'
    simp_rw [hssum, hsC, map_sum, map_mul, hms, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  refine ⟨fun j => ∑ l, C (ε l) * (c₀ l j).map (algebraMap 𝓞 E), ?_, ?_⟩
  ·
    show F = ∑ j, subst g (∑ l, C (ε l) * (c₀ l j).map (algebraMap 𝓞 E)) * (e₀ j).map (algebraMap 𝓞 E)
    rw [hkey]
    conv_lhs => rw [eq_sum_C_mul_map_comp ε F]
    exact Finset.sum_congr rfl fun l _ => by rw [← hc₀ l]
  ·
    intro c' hc'
    change F = ∑ j, subst g (c' j) * (e₀ j).map (algebraMap 𝓞 E) at hc'

    have hdec : ∀ j, c' j = ∑ l, C (ε l) * (comp ε l (c' j)).map (algebraMap 𝓞 E) := fun j => eq_sum_C_mul_map_comp ε (c' j)
    have hF : F = ∑ l, C (ε l) * (∑ j, subst g₀ (comp ε l (c' j)) * e₀ j).map (algebraMap 𝓞 E) := by
      rw [hc', ← hkey]
      exact Finset.sum_congr rfl fun j _ => by rw [← hdec j]
    have hcomp : ∀ l, (fun j => comp ε l (c' j)) = c₀ l := fun l =>
      hc₀u l _ (eq_comp_of_eq_sum ε F _ hF l).symm
    funext j
    rw [hdec j]
    exact Finset.sum_congr rfl fun l _ => by rw [← hcomp l]

end LVb

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm] (h : ℕ)
    (hh : Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ h)
    (E : Type v) [CommRing E] [Algebra 𝓞 E] [Module.Free 𝓞 E] [Module.Finite 𝓞 E] [Nontrivial E]
    (v : ℕ) (b : Fin d → E) (hb : ∀ i, b i ∈ (Ideal.span {(p : E)}).radical) :
    Module.Free E (MvPowerSeries (Fin d) E ⧸
        Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) - C (b i))) ∧
      Module.Finite E (MvPowerSeries (Fin d) E ⧸
        Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) - C (b i))) ∧
      Module.finrank E (MvPowerSeries (Fin d) E ⧸
        Ideal.span (Set.range fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E) - C (b i))) =
        p ^ (v * h) := by
  classical

  let g : Fin d → MvPowerSeries (Fin d) E := fun i => (Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E)
  let I : Ideal (MvPowerSeries (Fin d) E) := Ideal.span (Set.range fun i => g i - C (b i))
  show Module.Free E (MvPowerSeries (Fin d) E ⧸ I) ∧ Module.Finite E (MvPowerSeries (Fin d) E ⧸ I) ∧
    Module.finrank E (MvPowerSeries (Fin d) E ⧸ I) = p ^ (v * h)
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i => by
    show constantCoeff ((Φ.nthSeries (p ^ v) i).map (algebraMap 𝓞 E)) = 0
    rw [constantCoeff_map, MvFormalGroup.constantCoeff_nthSeries Φ _ i, map_zero]
  have hsg := hasSubst_of_constantCoeff_zero hg0
  have hsC : ∀ (x : E) (c : MvPowerSeries (Fin d) E), subst g (C x * c) = C x * subst g c := fun x c => by
    rw [← coe_substAlgHom hsg, map_mul]
    congr 1
    rw [c_eq_algebraMap, AlgHom.commutes]
  have hsC' : ∀ x : E, subst g (C x) = C x := fun x => by
    have := hsC x 1
    rwa [mul_one, ← coe_substAlgHom hsg, map_one, mul_one, coe_substAlgHom] at this
  have hsadd : ∀ c c' : MvPowerSeries (Fin d) E, subst g (c + c') = subst g c + subst g c' := fun c c' => by
    rw [← coe_substAlgHom hsg, map_add]
  have hsmul : ∀ c c' : MvPowerSeries (Fin d) E, subst g (c * c') = subst g c * subst g c' := fun c c' => by
    rw [← coe_substAlgHom hsg, map_mul]
  have hssum : ∀ (c : Fin d → MvPowerSeries (Fin d) E), subst g (∑ k, c k) = ∑ k, subst g (c k) := fun c => by
    rw [← coe_substAlgHom hsg, map_sum]
  have hsgen : ∀ i, subst g (X i - C (b i)) = g i - C (b i) := fun i => by
    rw [← coe_substAlgHom hsg, map_sub, coe_substAlgHom, subst_X hsg, hsC']

  haveI : IsAdicComplete (Ideal.span {(p : E)}) E := IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p E
  let ev : MvPowerSeries (Fin d) E →ₐ[E] E := MvFormalGroup.adicEvalAlgHom (R := E) (Ideal.span {(p : E)}) hb
  have hevC : ∀ x : E, ev (C x) = x := fun x => by
    show ev (algebraMap E (MvPowerSeries (Fin d) E) x) = x
    rw [AlgHom.commutes]; rfl
  have hevX : ∀ i, ev (X i) = b i := fun i => by
    show MvFormalGroup.adicEvalAlgHom (R := E) (Ideal.span {(p : E)}) hb (X i) = b i
    rw [MvFormalGroup.coe_adicEvalAlgHom, MvFormalGroup.adicEval_X]
  have hevgen : ∀ (i : Fin d) (c : MvPowerSeries (Fin d) E), ev ((X i - C (b i)) * c) = 0 := fun i c => by
    rw [map_mul, map_sub, hevX, hevC, sub_self, zero_mul]

  obtain ⟨e, he⟩ := LVb.stepA p hp Φ h hh E v
  choose coord hcoord using fun F => (he F).exists
  have hcu : ∀ (F : MvPowerSeries (Fin d) E) (c' : Fin (p ^ (v * h)) → MvPowerSeries (Fin d) E),
      F = ∑ j, subst g (c' j) * e j → c' = coord F := fun F c' hc' => (he F).unique hc' (hcoord F)
  have coord_add : ∀ F G, coord (F + G) = coord F + coord G := fun F G => by
    refine (hcu (F + G) _ ?_).symm
    conv_lhs => rw [hcoord F, hcoord G]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, hsadd, add_mul]
  have coord_smul : ∀ (x : E) F, coord (x • F) = fun j => C x * coord F j := fun x F => by
    refine (hcu (x • F) _ ?_).symm
    conv_lhs => rw [hcoord F]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, hsC, mul_assoc]

  let φ : MvPowerSeries (Fin d) E →ₗ[E] (Fin (p ^ (v * h)) → E) :=
    { toFun := fun F j => ev (coord F j)
      map_add' := fun F G => by funext j; simp only [Pi.add_apply, coord_add, map_add]
      map_smul' := fun x F => by
        funext j
        simp only [Pi.smul_apply, coord_smul, map_mul, hevC, RingHom.id_apply, smul_eq_mul] }
  have hφ : ∀ F j, φ F j = ev (coord F j) := fun F j => rfl

  have hφsurj : Function.Surjective φ := by
    intro y
    refine ⟨∑ j, C (y j) * e j, ?_⟩
    have hc : coord (∑ j, C (y j) * e j) = fun j => C (y j) :=
      (hcu _ _ (Finset.sum_congr rfl fun j _ => by rw [hsC'])).symm
    funext j
    rw [hφ, hc, hevC]

  have hker : LinearMap.ker φ = I.restrictScalars E := by
    apply le_antisymm
    · intro F hF
      rw [LinearMap.mem_ker] at hF
      rw [Submodule.restrictScalars_mem]

      have hq : ∀ j, ∃ q : Fin d → MvPowerSeries (Fin d) E, coord F j = ∑ i, (X i - C (b i)) * q i := by
        intro j
        obtain ⟨r, q, hrq⟩ :=
          MvPowerSeries.exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete (Ideal.span {(p : E)}) b hb (coord F j)
        have hr : r = 0 := by
          have h0 : ev (coord F j) = 0 := congrFun hF j
          rw [hrq, map_add, hevC, map_sum] at h0
          simpa only [hevgen, Finset.sum_const_zero, add_zero] using h0
        exact ⟨q, by rw [hrq, hr, map_zero, zero_add]⟩
      choose q hq using hq
      rw [hcoord F]
      refine I.sum_mem fun j _ => I.mul_mem_right _ ?_
      rw [hq j, hssum]
      refine I.sum_mem fun i _ => ?_
      rw [hsmul, hsgen]
      exact I.mul_mem_right _ (Ideal.subset_span ⟨i, rfl⟩)
    · intro F hF
      rw [Submodule.restrictScalars_mem] at hF
      rw [LinearMap.mem_ker]
      obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF

      have hc : coord F = fun j => ∑ i, (X i - C (b i)) * coord (a i) j := by
        refine (hcu F _ ?_).symm
        rw [← ha]
        simp_rw [hssum, hsmul, hsgen, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [hcoord (a i), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      funext j
      rw [hφ, hc]
      simp only [map_sum, hevgen, Finset.sum_const_zero, Pi.zero_apply]

  let eqv : (MvPowerSeries (Fin d) E ⧸ I) ≃ₗ[E] (Fin (p ^ (v * h)) → E) :=
    (Submodule.Quotient.restrictScalarsEquiv E I).symm ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hker.symm) ≪≫ₗ (LinearMap.quotKerEquivOfSurjective φ hφsurj)
  refine ⟨Module.Free.of_equiv eqv.symm, Module.Finite.equiv eqv.symm, ?_⟩
  rw [eqv.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

end S_MvFormalGroup_free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial
end P2MW
export P2MW.S_MvFormalGroup_free_and_finrank_quotient_span_nthSeries_sub_C_eq_pow_of_nontrivial (solution)
