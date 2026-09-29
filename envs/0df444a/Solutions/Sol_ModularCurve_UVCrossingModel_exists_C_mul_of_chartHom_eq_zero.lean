-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_C_mul_of_chartHom_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/31fad832-a517-57b0-bfbb-205cd3710583

import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel"
p2m_open "ModularCurve"

namespace PortB5

p2m_open "ModularCurve.UVCrossingModel"

universe u

section KillVariable

variable {W : Type u} [CommRing W]

def uBranchEmb : Unit ↪ Fin 2 :=
  ⟨fun _ => 1, fun a b _ => Subsingleton.elim a b⟩

def vBranchEmb : Unit ↪ Fin 2 :=
  ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

@[scoped simp] theorem uBranchEmb_apply (x : Unit) : uBranchEmb x = 1 := rfl

@[scoped simp] theorem vBranchEmb_apply (x : Unit) : vBranchEmb x = 0 := rfl

theorem zero_notMem_range_uBranchEmb : (0 : Fin 2) ∉ Set.range uBranchEmb := by
  rintro ⟨x, hx⟩
  rw [uBranchEmb_apply] at hx
  exact absurd hx (by decide)

theorem one_notMem_range_vBranchEmb : (1 : Fin 2) ∉ Set.range vBranchEmb := by
  rintro ⟨x, hx⟩
  rw [vBranchEmb_apply] at hx
  exact absurd hx (by decide)

theorem uBranchEmb_cover : ∀ j : Fin 2, j ≠ 0 → j = uBranchEmb () := by decide

theorem vBranchEmb_cover : ∀ j : Fin 2, j ≠ 1 → j = vBranchEmb () := by decide

def killVarHom (e : Unit ↪ Fin 2) : MvPowerSeries (Fin 2) W →+* MvPowerSeries Unit W :=
  (MvPowerSeries.killCompl e).toRingHom

@[scoped simp] theorem killVarHom_apply (e : Unit ↪ Fin 2) (φ : MvPowerSeries (Fin 2) W) :
    killVarHom e φ = MvPowerSeries.killCompl e φ := rfl

theorem killVarHom_X_keep (e : Unit ↪ Fin 2) :
    killVarHom (W := W) e (MvPowerSeries.X (e ())) = PowerSeries.X :=
  MvPowerSeries.killCompl_X ()

theorem killVarHom_X_kill (e : Unit ↪ Fin 2) {t : Fin 2} (ht : t ∉ Set.range e) :
    killVarHom (W := W) e (MvPowerSeries.X t) = 0 :=
  MvPowerSeries.killCompl_X_eq_zero ht

theorem killVarHom_C (e : Unit ↪ Fin 2) (w : W) :
    killVarHom e (MvPowerSeries.C w) = PowerSeries.C w :=
  MvPowerSeries.killCompl_C w

theorem killVarHom_surjective (e : Unit ↪ Fin 2) :
    Function.Surjective (killVarHom (W := W) e) := fun q =>
  ⟨MvPowerSeries.rename (⇑e) q, MvPowerSeries.killCompl_rename_app q⟩

theorem ker_killVarHom (e : Unit ↪ Fin 2) (t : Fin 2) (ht : t ∉ Set.range e)
    (hcover : ∀ j : Fin 2, j ≠ t → j = e ()) :
    RingHom.ker (killVarHom (W := W) e) =
      Ideal.span {(MvPowerSeries.X t : MvPowerSeries (Fin 2) W)} := by
  refine le_antisymm (fun φ hφ => ?_) ?_
  · rw [RingHom.mem_ker] at hφ
    have hφ' : MvPowerSeries.killCompl e φ = 0 := hφ
    rw [Ideal.mem_span_singleton, MvPowerSeries.X_dvd_iff]
    intro m hm
    have hne : e () ≠ t := fun h => ht (h ▸ Set.mem_range_self ())
    have hm_eq : m = Finsupp.embDomain e (Finsupp.single () (m (e ()))) := by
      rw [Finsupp.embDomain_single]
      ext j
      rcases eq_or_ne j t with hj | hj
      · rw [hj, hm, Finsupp.single_eq_of_ne' hne]
      · rw [hcover j hj, Finsupp.single_eq_same]
    rw [hm_eq, ← MvPowerSeries.coeff_killCompl, hφ', map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact killVarHom_X_kill e ht

end KillVariable

section AmbientRetraction

variable (W : Type u) [CommRing W]

def killVSubstFamily : Fin 2 → MvPowerSeries Unit W :=
  ![MvPowerSeries.X (), 0]

theorem hasSubst_killVSubstFamily : MvPowerSeries.HasSubst (killVSubstFamily W) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s <;> simp [killVSubstFamily]

theorem prod_killVSubstFamily (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => killVSubstFamily W s ^ n) =
      MvPowerSeries.X (R := W) () ^ d 0 * (0 : MvPowerSeries Unit W) ^ d 1 := by
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero _, Fin.prod_univ_two,
    show killVSubstFamily W 0 = MvPowerSeries.X () from rfl,
    show killVSubstFamily W 1 = (0 : MvPowerSeries Unit W) from rfl]

theorem killVarHom_vBranchEmb_eq_subst (φ : MvPowerSeries (Fin 2) W) :
    killVarHom vBranchEmb φ = MvPowerSeries.subst (killVSubstFamily W) φ := by
  classical
  refine MvPowerSeries.ext fun x => ?_
  have hx : Finsupp.embDomain vBranchEmb x = Finsupp.single (0 : Fin 2) (x ()) := by
    conv_lhs => rw [Finsupp.unique_single x]
    rw [Finsupp.embDomain_single]
    rfl
  rw [killVarHom_apply, MvPowerSeries.coeff_killCompl, hx,
    MvPowerSeries.coeff_subst (hasSubst_killVSubstFamily W) φ x]
  symm
  refine (finsum_eq_single _ (Finsupp.single (0 : Fin 2) (x ())) fun d hd => ?_).trans ?_
  ·
    rw [prod_killVSubstFamily]
    rcases eq_or_ne (d 1) 0 with h1 | h1
    ·
      have hne : x ≠ Finsupp.single () (d 0) := by
        intro hxd
        apply hd
        have hx0 : x () = d 0 := by rw [hxd]; exact Finsupp.single_eq_same
        refine Finsupp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rw [Finsupp.single_eq_same, hx0]
        · rw [h1, Finsupp.single_eq_of_ne (by decide)]
      rw [h1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow, if_neg hne, smul_zero]
    ·
      rw [zero_pow h1, mul_zero, map_zero, smul_zero]
  ·
    rw [prod_killVSubstFamily, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), pow_zero, mul_one,
      MvPowerSeries.coeff_X_pow, if_pos (Finsupp.unique_single x), smul_eq_mul, mul_one]

theorem subst_killVSubstFamily_sAmbient :
    MvPowerSeries.subst (killVSubstFamily W) (sAmbient W) = MvPowerSeries.X () := by
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_killVSubstFamily W), sAmbient_def, map_add,
    MvPowerSeries.substAlgHom_X, MvPowerSeries.substAlgHom_X,
    show killVSubstFamily W 0 = MvPowerSeries.X () from rfl,
    show killVSubstFamily W 1 = (0 : MvPowerSeries Unit W) from rfl, add_zero]

theorem killVarHom_vBranchEmb_subst_sAmbient (f : PowerSeries W) :
    killVarHom vBranchEmb (PowerSeries.subst (sAmbient W) f) = f := by
  rw [killVarHom_vBranchEmb_eq_subst, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.const (hasSubst_sAmbient W)) (hasSubst_killVSubstFamily W)]
  simp only [subst_killVSubstFamily_sAmbient]
  rw [show (fun _ : Unit => MvPowerSeries.X (R := W) ()) =
      (MvPowerSeries.X : Unit → MvPowerSeries Unit W) from funext fun _ => rfl,
    ← MvPowerSeries.map_algebraMap_eq_subst_X, Algebra.algebraMap_self,
    MvPowerSeries.map_id]
  rfl

theorem subst_sAmbient_injective :
    Function.Injective fun f : PowerSeries W => PowerSeries.subst (sAmbient W) f :=
  Function.LeftInverse.injective (g := killVarHom vBranchEmb)
    (killVarHom_vBranchEmb_subst_sAmbient W)

end AmbientRetraction

section ModPiIteration

variable {W : Type u} [CommRing W]

theorem exists_C_mul_of_chartHom_eq_zero {π : W} {f : PowerSeries W}
    (hf : chartHom π f = 0) :
    ∃ g : PowerSeries W, f = PowerSeries.C π * g := by
  rw [chartHom_apply] at hf
  have hmem : PowerSeries.subst (sAmbient W) f ∈ uvCrossingIdeal W π :=
    Ideal.Quotient.eq_zero_iff_mem.mp hf
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem
  have hkeep : killVarHom (W := W) vBranchEmb (MvPowerSeries.X 0) = PowerSeries.X :=
    killVarHom_X_keep vBranchEmb
  have hkill : killVarHom (W := W) vBranchEmb (MvPowerSeries.X 1) = 0 :=
    killVarHom_X_kill vBranchEmb one_notMem_range_vBranchEmb
  have h1 := congrArg (killVarHom (W := W) vBranchEmb) hg
  rw [killVarHom_vBranchEmb_subst_sAmbient, map_mul, map_sub, map_mul, hkeep, hkill,
    killVarHom_C, mul_zero, zero_sub] at h1
  refine ⟨-(killVarHom vBranchEmb g), ?_⟩
  rw [← h1]
  ring

theorem exists_pow_C_mul_of_chartHom_eq_zero {π : W}
    (hcancel : const π π ∈ nonZeroDivisors (UVCrossingModel W π))
    {f : PowerSeries W} (hf : chartHom π f = 0) (n : ℕ) :
    ∃ g : PowerSeries W, f = PowerSeries.C π ^ n * g ∧ chartHom π g = 0 := by
  induction n with
  | zero => exact ⟨f, by rw [pow_zero, one_mul], hf⟩
  | succ n ih =>
    obtain ⟨g, hg, hg0⟩ := ih
    obtain ⟨g₁, hg₁⟩ := exists_C_mul_of_chartHom_eq_zero hg0
    refine ⟨g₁, by rw [hg, hg₁, pow_succ]; ring, ?_⟩
    have h2 : chartHom π g₁ * const π π = 0 := by
      rw [mul_comm, ← chartHom_C, ← map_mul, ← hg₁, hg0]
    exact (mem_nonZeroDivisors_iff.mp hcancel).2 _ h2

theorem pow_dvd_coeff_of_chartHom_eq_zero {π : W}
    (hcancel : const π π ∈ nonZeroDivisors (UVCrossingModel W π))
    {f : PowerSeries W} (hf : chartHom π f = 0) (n m : ℕ) :
    π ^ n ∣ PowerSeries.coeff m f := by
  obtain ⟨g, hg, -⟩ := exists_pow_C_mul_of_chartHom_eq_zero hcancel hf n
  rw [hg, ← map_pow, PowerSeries.coeff_C_mul]
  exact dvd_mul_right _ _

theorem chartHom_injective_of_forall_pow_dvd {π : W}
    (hcancel : const π π ∈ nonZeroDivisors (UVCrossingModel W π))
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) :
    Function.Injective (chartHom π) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  refine PowerSeries.ext fun m => ?_
  rw [map_zero]
  exact hsep _ fun n => pow_dvd_coeff_of_chartHom_eq_zero hcancel hf n m

theorem chartHom_zero_injective :
    Function.Injective (chartHom (0 : W)) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf => ?_
  obtain ⟨g, hg⟩ := exists_C_mul_of_chartHom_eq_zero hf
  rw [hg, map_zero, zero_mul]

end ModPiIteration

end PortB5
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.ModularCurve.PortB5"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.ModularCurve.PortB5 P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.ModularCurve.PortB5 P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] {π : W} {f : PowerSeries W} (hf : chartHom π f = 0) :
    ∃ g : PowerSeries W, f = PowerSeries.C π * g :=
  ModularCurve.PortB5.exists_C_mul_of_chartHom_eq_zero hf

end S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero (solution)
