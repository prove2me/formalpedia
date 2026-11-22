-- Prove2me | solution 1 for MasulloGRH.tateArchimedeanDomain_torsion_translates
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:39:03.713904+00:00
-- url     : https://prove2.me/submissions/60ccae6a-05e6-4b57-a775-2436ce554fd0

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tateArchimedeanDomain_torsion_translates

open NumberField InfinitePlace.Completion MasulloGRH RiemannMasullo

variable (F : Type*) [Field F] [NumberField F]

omit [NumberField F] in
/-- The archimedean logarithm takes products to sums. -/
theorem infiniteIdeleLog_mul (g h : (InfiniteAdeleRing F)ˣ) :
    infiniteIdeleLog F (g * h) = infiniteIdeleLog F g + infiniteIdeleLog F h := by
  have hne (u : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) : u.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom u).ne_zero
  funext v
  change (v.mult : ℝ) * Real.log ‖(g.val * h.val) v‖ =
    v.mult * Real.log ‖g.val v‖ + v.mult * Real.log ‖h.val v‖
  rw [← mul_add, ← Real.log_mul (norm_ne_zero_iff.mpr (hne g v)) (norm_ne_zero_iff.mpr (hne h v)),
    ← norm_mul]
  rfl

/-- The archimedean logarithm as a homomorphism to a torsion-free group. -/
noncomputable def logHom : (InfiniteAdeleRing F)ˣ →* Multiplicative (InfinitePlace F → ℝ) :=
  MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (infiniteIdeleLog F g)) (infiniteIdeleLog_mul F)

/-- The diagonal image of a root of unity has norm one. -/
theorem norm_torsion (u : (𝓞 F)ˣ) (hu : u ∈ Units.torsion F) :
    infiniteIdeleNorm F (unitsToInfiniteIdeles F u) = 1 := by
  have hfin : IsOfFinOrder u := (CommGroup.mem_torsion u).mp hu
  exact (((infiniteIdeleNorm F).comp (unitsToInfiniteIdeles F)).isOfFinOrder hfin).eq_one'

omit [NumberField F] in
/-- The diagonal image of a root of unity has zero logarithm. -/
theorem log_torsion (u : (𝓞 F)ˣ) (hu : u ∈ Units.torsion F) :
    infiniteIdeleLog F (unitsToInfiniteIdeles F u) = 0 := by
  have hfin : IsOfFinOrder u := (CommGroup.mem_torsion u).mp hu
  exact (((logHom F).comp (unitsToInfiniteIdeles F)).isOfFinOrder hfin).eq_one'

omit [NumberField F] in
/-- Multiplying by the diagonal image of a root of unity does not change the logarithm. -/
theorem log_torsion_mul (u : (𝓞 F)ˣ) (hu : u ∈ Units.torsion F) (g : (InfiniteAdeleRing F)ˣ) :
    infiniteIdeleLog F (unitsToInfiniteIdeles F u * g) = infiniteIdeleLog F g := by
  rw [infiniteIdeleLog_mul, log_torsion F u hu, zero_add]

/-- A diagonal root of unity moves an archimedean idele into the chosen angular sector. -/
theorem exists_torsionUnit_mul_mem_inTorsionSector (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (g : (InfiniteAdeleRing F)ˣ) :
    ∃ u ∈ Units.torsion F, inTorsionSector F v₀ σ
      (Units.map (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v₀).toMonoidHom
        (unitsToInfiniteIdeles F u * g)) := by
  let f : (InfiniteAdeleRing F)ˣ →* ℂˣ :=
    (Units.map (σ.toRingHom.comp (extensionEmbedding v₀)).toMonoidHom).comp
      (Units.map (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v₀).toMonoidHom)
  let φ : F →+* ℂ := σ.toRingHom.comp ((extensionEmbedding v₀).comp
    ((Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v₀).comp
      (algebraMap F (InfiniteAdeleRing F))))
  let z : ℂ := (f g).val
  let n := Units.torsionOrder F
  let p := 2 * Real.pi / (n : ℝ)
  have hn : 0 < (n : ℝ) := by exact_mod_cast Units.torsionOrder_pos F
  have hp : 0 < p := div_pos Real.two_pi_pos hn
  have hn₂ : (2 : ℝ) ≤ n := by
    obtain ⟨m, hm⟩ := Units.even_torsionOrder F
    have := Units.torsionOrder_pos F
    exact_mod_cast (by omega : 2 ≤ Units.torsionOrder F)
  have hpπ : p ≤ Real.pi := (div_le_iff₀ hn).mpr (by
    simpa only [mul_comm Real.pi] using mul_le_mul_of_nonneg_right hn₂ Real.pi_pos.le)
  obtain ⟨k, hk, -⟩ := existsUnique_add_zsmul_mem_Ico hp z.arg 0
  rw [zero_add] at hk
  let w := Complex.exp ((p : ℂ) * Complex.I)
  have hw : w ^ n = 1 := by
    simpa [w, p, div_mul_eq_mul_div] using
      (Complex.isPrimitiveRoot_exp n (Units.torsionOrder_ne_zero F)).pow_eq_one
  let ζ : ℂˣ := Units.mk0 w (Complex.exp_ne_zero _)
  have hζ : ζ ∈ rootsOfUnity n ℂ := (mem_rootsOfUnity' n ζ).mpr hw
  rw [← Units.map_complexEmbedding_torsion F φ] at hζ
  obtain ⟨u, hu, hmap⟩ := hζ
  have hunit : f (unitsToInfiniteIdeles F u) = ζ := hmap
  have hrotate : w ^ k * z =
      (‖z‖ : ℂ) * Complex.exp (((z.arg + k • p : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = w ^ k * ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * Complex.I)) :=
        congrArg (w ^ k * ·) (Complex.norm_mul_exp_arg_mul_I z).symm
      _ = _ := by
        dsimp only [w]
        rw [← Complex.exp_int_mul, zsmul_eq_mul]
        push_cast
        rw [add_mul, Complex.exp_add, mul_assoc (k : ℂ) (p : ℂ) Complex.I]
        ring
  refine ⟨u ^ k, Subgroup.zpow_mem _ hu k, ?_⟩
  change (f (unitsToInfiniteIdeles F (u ^ k) * g)).val.arg ∈ Set.Ico 0 p
  rw [map_mul, map_zpow, map_zpow, hunit, Units.val_mul, Units.val_zpow_eq_zpow_val]
  change (w ^ k * z).arg ∈ Set.Ico 0 p
  rw [hrotate, Complex.arg_real_mul _ (norm_pos_iff.mpr (f g).ne_zero),
    Complex.arg_exp_mul_I, (toIocMod_eq_self Real.two_pi_pos).mpr]
  · exact hk
  · refine ⟨(neg_lt_zero.mpr Real.pi_pos).trans_le hk.1, ?_⟩
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact hk.2.le.trans hpπ

end Sol_MasulloGRH_tateArchimedeanDomain_torsion_translates

open MasulloGRH Sol_MasulloGRH_tateArchimedeanDomain_torsion_translates in
theorem solution
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (g : MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :
    g ∈ logParallelotopePreimage F b ↔
      ∃ ζ ∈ Units.torsion F, ∃ e ∈ tateArchimedeanDomain F b v₀ σ,
        (g : (InfiniteAdeleRing F)ˣ) =
          unitsToInfiniteIdeles F ζ * (e : (InfiniteAdeleRing F)ˣ) := by
  constructor
  · intro hg
    obtain ⟨u, hu, hsec⟩ := exists_torsionUnit_mul_mem_inTorsionSector F v₀ σ g.val
    have hker : unitsToInfiniteIdeles F u * g.val ∈
        MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F) :=
      mul_mem (MonoidHom.mem_ker.mpr (norm_torsion F u hu)) g.property
    refine ⟨u⁻¹, inv_mem hu, ⟨unitsToInfiniteIdeles F u * g.val, hker⟩, ⟨?_, hsec⟩, ?_⟩
    · change (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦
          RiemannMasullo.infiniteIdeleLog F (unitsToInfiniteIdeles F u * g.val) w.val) ∈
        RiemannMasullo.regulatorParallelotope F b
      rw [log_torsion_mul F u hu]
      exact hg
    · change g.val = unitsToInfiniteIdeles F u⁻¹ * (unitsToInfiniteIdeles F u * g.val)
      rw [map_inv, inv_mul_cancel_left]
  · rintro ⟨ζ, hζ, e, he, hge⟩
    change (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦
        RiemannMasullo.infiniteIdeleLog F g.val w.val) ∈
      RiemannMasullo.regulatorParallelotope F b
    rw [hge, log_torsion_mul F ζ hζ]
    exact he.1
