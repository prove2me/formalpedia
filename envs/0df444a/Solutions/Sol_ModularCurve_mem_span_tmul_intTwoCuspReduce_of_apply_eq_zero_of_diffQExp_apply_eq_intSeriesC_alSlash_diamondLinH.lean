-- Prove2me | solution 1 for ModularCurve.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bd86e3f7-8942-5f8b-ae56-10c11ffbd07e

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped TensorProduct ModularForm MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup Gamma1_le_GammaH IsIntegralQExp isIntegralQExp_iff IsIntegralQExp.unique isIntegralQExp_zero intSeriesC intSeriesC_zero qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_ofPowerSeries diffQExp"
namespace LinAuxW
p2m_open "ModularCurve"

def toZ (a : (⊥ : Subring ℂ)) : ℤ := (Subring.mem_bot.mp a.2).choose

theorem cast_toZ (a : (⊥ : Subring ℂ)) : ((toZ a : ℤ) : ℂ) = (a : ℂ) := (Subring.mem_bot.mp a.2).choose_spec

theorem toZ_add (a b : (⊥ : Subring ℂ)) : toZ (a + b) = toZ a + toZ b := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_add, cast_toZ, cast_toZ, cast_toZ, Subring.coe_add]

theorem toZ_mul (a b : (⊥ : Subring ℂ)) : toZ (a * b) = toZ a * toZ b := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_mul, cast_toZ, cast_toZ, cast_toZ, Subring.coe_mul]

theorem toZ_one : toZ 1 = 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_one, Subring.coe_one]

theorem toZ_zero : toZ 0 = 0 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_zero, Subring.coe_zero]

theorem toZ_natCast (n : ℕ) : toZ (n : (⊥ : Subring ℂ)) = n := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_natCast]; rfl

def toZHom : (⊥ : Subring ℂ) →+* ℤ where
  toFun := toZ
  map_one' := toZ_one
  map_mul' := toZ_mul
  map_zero' := toZ_zero
  map_add' := toZ_add

theorem smul_eq_toZ_zsmul {V : Type*} [AddCommGroup V] [Module ℂ V] (a : (⊥ : Subring ℂ)) (v : V) :
    a • v = toZ a • v := by
  rw [Subring.smul_def, ← cast_toZ, Int.cast_smul_eq_zsmul]

theorem ofPowerSeries_coeff_neg {R : Type*} [CommRing R] (x : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  have hm' : (m : ℤ) = n := hm
  omega

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ofPowerSeries_coeff_neg _ hn, ofPowerSeries_coeff_neg _ hn, map_zero]
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

section Iota

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra (ZMod p) K]

def ιL : K ⊗[ZMod p] LaurentSeries (ZMod p) →ₗ[ZMod p] LaurentSeries K :=
  TensorProduct.lift
    (LinearMap.mk₂ (ZMod p) (fun (c : K) (f : LaurentSeries (ZMod p)) => c • coeffMap (algebraMap (ZMod p) K) f)
      (fun c d f => by rw [add_smul])
      (fun r c f => by rw [smul_assoc])
      (fun c f g => by rw [map_add, smul_add])
      (fun r c f => by
        ext n
        simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul, Algebra.smul_def]
        ring))

theorem ιL_tmul (c : K) (f : LaurentSeries (ZMod p)) :
    ιL p K (c ⊗ₜ[ZMod p] f) = c • coeffMap (algebraMap (ZMod p) K) f :=
  TensorProduct.lift.tmul c f

theorem ιL_injective : Function.Injective (ιL p K) :=
  LaurentSeries.injective_of_forall_apply_tmul_eq_smul_map (ZMod p) K (ιL p K) (fun a f => ιL_tmul p K a f)

def ofPS : PowerSeries (ZMod p) →ₗ[ZMod p] LaurentSeries (ZMod p) where
  toFun := HahnSeries.ofPowerSeries ℤ (ZMod p)
  map_add' s t := map_add _ s t
  map_smul' r s := by
    rw [RingHom.id_apply, PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem ofPS_apply (s : PowerSeries (ZMod p)) : ofPS p s = HahnSeries.ofPowerSeries ℤ (ZMod p) s := rfl

theorem ofPS_injective : Function.Injective (ofPS p) := fun a b h => HahnSeries.ofPowerSeries_injective h

theorem ι_injective : Function.Injective (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) := by
  rw [LinearMap.coe_comp]
  exact (ιL_injective p K).comp (Module.Flat.lTensor_preserves_injective_linearMap _ (ofPS_injective p))

theorem ι_tmul (c : K) (s : PowerSeries (ZMod p)) :
    (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) (c ⊗ₜ[ZMod p] s) =
      c • HahnSeries.ofPowerSeries ℤ K (s.map (algebraMap (ZMod p) K)) := by
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, ιL_tmul, ofPS_apply, coeffMap_ofPowerSeries]

end Iota

section Main

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
  (K : Type*) [Field K] [Algebra (ZMod p) K]

local notation "Γ" => CohCarrier.GammaH M H
local notation "A" => (⊥ : Subring ℂ)
local notation "L" => CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)
local notation "Ω₀" => CuspForm.IntTwoCuspForms M H p
local notation "F̄" => qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))

theorem Gamma1_le_GammaH : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro g hg
  rw [CongruenceSubgroup.Gamma1_mem] at hg
  obtain ⟨h00, h11, h10⟩ := hg
  have hg0 : g ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hg0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨g, hg0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have h1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    show (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples _
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact Subgroup.map_mono (Gamma1_le_GammaH M H) h1

theorem qExpansion_coe_add (f g : CuspForm Γ 2) :
    UpperHalfPlane.qExpansion 1 ⇑(f + g) = UpperHalfPlane.qExpansion 1 ⇑f + UpperHalfPlane.qExpansion 1 ⇑g :=
  ModularFormClass.qExpansion_add one_pos (one_mem_strictPeriods M H) f g

theorem qExpansion_coe_smul (c : ℂ) (f : CuspForm Γ 2) :
    UpperHalfPlane.qExpansion 1 ⇑(c • f) = c • UpperHalfPlane.qExpansion 1 ⇑f :=
  ModularFormClass.qExpansion_smul one_pos (one_mem_strictPeriods M H) c f

variable (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
  (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)

include hHp in
omit [Fact p.Prime] in

theorem exists_Xf (hp : p.Prime) (F : CuspForm Γ 2) :
    ∃ X : CuspForm Γ 2, ⇑X = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e F) := by
  have hHp' : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
    obtain ⟨R, hM, a, b, bez⟩ := W
    have hR : R = M / p := by
      subst hM
      exact (Nat.mul_div_cancel_left R hp.pos).symm
    subst hR
    exact hHp
  exact CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp' 2 (CuspForm.diamondLinH 2 e F)

def Xf (F : CuspForm Γ 2) : CuspForm Γ 2 := (exists_Xf p M hpM H hHp W e Fact.out F).choose

theorem coe_Xf (F : CuspForm Γ 2) : ⇑(Xf p M hpM H hHp W e F) = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e F) :=
  (exists_Xf p M hpM H hHp W e Fact.out F).choose_spec

theorem Xf_add (F G : CuspForm Γ 2) : Xf p M hpM H hHp W e (F + G) = Xf p M hpM H hHp W e F + Xf p M hpM H hHp W e G := by
  apply DFunLike.ext'
  rw [CuspForm.coe_add, coe_Xf, coe_Xf, coe_Xf, map_add, CuspForm.coe_add, ModularForm.alSlash_add]

theorem Xf_smul (c : ℂ) (F : CuspForm Γ 2) : Xf p M hpM H hHp W e (c • F) = c • Xf p M hpM H hHp W e F := by
  apply DFunLike.ext'
  have h1 : ⇑(c • Xf p M hpM H hHp W e F) = c • ⇑(Xf p M hpM H hHp W e F) := by
    funext z; rfl
  have h2 : ⇑(c • CuspForm.diamondLinH 2 e F) = c • ⇑(CuspForm.diamondLinH 2 e F) := by
    funext z; rfl
  rw [h1, coe_Xf, coe_Xf, map_smul, h2, ModularForm.alSlash_smul]

theorem Xf_zsmul (n : ℤ) (F : CuspForm Γ 2) : Xf p M hpM H hHp W e (n • F) = n • Xf p M hpM H hHp W e F := by
  rw [← Int.cast_smul_eq_zsmul ℂ n F, Xf_smul, Int.cast_smul_eq_zsmul]

theorem Xf_zero : Xf p M hpM H hHp W e 0 = 0 := by
  have h := Xf_smul p M hpM H hHp W e 0 0
  rwa [zero_smul, zero_smul] at h

theorem isIntegralQExp_add {f g : CuspForm Γ 2} {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp ⇑f pf)
    (hg : IsIntegralQExp ⇑g pg) : IsIntegralQExp ⇑(f + g) (pf + pg) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [map_add, hf, hg, qExpansion_coe_add]

theorem isIntegralQExp_zsmul {f : CuspForm Γ 2} {pf : PowerSeries ℤ} (hf : IsIntegralQExp ⇑f pf) (n : ℤ) :
    IsIntegralQExp ⇑(n • f) (n • pf) := by
  unfold IsIntegralQExp at hf ⊢
  rw [map_zsmul, hf, ← Int.cast_smul_eq_zsmul ℂ n f, qExpansion_coe_smul, Int.cast_smul_eq_zsmul]

theorem exists_isIntegralQExp (f : CuspForm Γ 2) (hf : f ∈ L) : ∃ pf : PowerSeries ℤ, IsIntegralQExp ⇑(Xf p M hpM H hHp W e f) pf := by
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    have hc : ∀ n, ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) n ∈ A := fun n => by
      have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hfS) (CuspForm.diamondLinH 2 e)
        (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia e)) W n
      exact h.2
    refine ⟨PowerSeries.mk fun n => toZ ⟨_, hc n⟩, ?_⟩
    rw [coe_Xf, isIntegralQExp_iff]
    intro n
    rw [PowerSeries.coeff_mk, cast_toZ]
    rfl
  | zero => exact ⟨0, by rw [Xf_zero]; simpa using isIntegralQExp_zero⟩
  | add f g _ _ hf hg =>
    obtain ⟨pf, hpf⟩ := hf
    obtain ⟨pg, hpg⟩ := hg
    exact ⟨pf + pg, by rw [Xf_add]; exact isIntegralQExp_add M H hpf hpg⟩
  | smul a f _ hf =>
    obtain ⟨pf, hpf⟩ := hf
    refine ⟨toZ a • pf, ?_⟩
    rw [smul_eq_toZ_zsmul, Xf_zsmul]
    exact isIntegralQExp_zsmul M H hpf (toZ a)

def expZ (y : L) : PowerSeries ℤ := (exists_isIntegralQExp p M hpM H hHp W e (y : CuspForm Γ 2) y.2).choose

theorem isIntegralQExp_expZ (y : L) : IsIntegralQExp ⇑(Xf p M hpM H hHp W e (y : CuspForm Γ 2)) (expZ p M hpM H hHp W e y) :=
  (exists_isIntegralQExp p M hpM H hHp W e (y : CuspForm Γ 2) y.2).choose_spec

theorem expZ_add (y y' : L) : expZ p M hpM H hHp W e (y + y') = expZ p M hpM H hHp W e y + expZ p M hpM H hHp W e y' := by
  have h := isIntegralQExp_expZ p M hpM H hHp W e (y + y')
  rw [Submodule.coe_add, Xf_add] at h
  exact h.unique (isIntegralQExp_add M H (isIntegralQExp_expZ p M hpM H hHp W e y) (isIntegralQExp_expZ p M hpM H hHp W e y'))

theorem expZ_smul (a : A) (y : L) : expZ p M hpM H hHp W e (a • y) = toZ a • expZ p M hpM H hHp W e y := by
  refine (isIntegralQExp_expZ p M hpM H hHp W e (a • y)).unique ?_
  have : ((a • y : L) : CuspForm Γ 2) = toZ a • (y : CuspForm Γ 2) := by
    rw [Submodule.coe_smul, smul_eq_toZ_zsmul]
  rw [this, Xf_zsmul]
  exact isIntegralQExp_zsmul M H (isIntegralQExp_expZ p M hpM H hHp W e y) (toZ a)

theorem cast_coeff_expZ (y : L) (n : ℕ) :
    ((PowerSeries.coeff n (expZ p M hpM H hHp W e y) : ℤ) : ℂ) = ModularFormClass.qCoeff ⇑(Xf p M hpM H hHp W e (y : CuspForm Γ 2)) n :=
  (isIntegralQExp_expZ p M hpM H hHp W e y).coeff n

def redA : A →+* ZMod p := (Int.castRingHom (ZMod p)).comp toZHom

theorem redA_apply (a : A) : redA p a = (toZ a : ZMod p) := rfl

@[reducible] def modA : Module A (PowerSeries (ZMod p)) := Module.compHom _ (redA p)

theorem psi_aux_smul (a : A) (y : L) :
    (expZ p M hpM H hHp W e (a • y)).map (Int.castRingHom (ZMod p)) =
      letI := modA p; a • (expZ p M hpM H hHp W e y).map (Int.castRingHom (ZMod p)) := by
  letI := modA p
  rw [expZ_smul, map_zsmul]
  show _ = redA p a • (expZ p M hpM H hHp W e y).map (Int.castRingHom (ZMod p))
  rw [redA_apply, Int.cast_smul_eq_zsmul]

def ψ : letI := modA p; L →ₗ[A] PowerSeries (ZMod p) :=
  letI := modA p
  { toFun := fun y => (expZ p M hpM H hHp W e y).map (Int.castRingHom (ZMod p))
    map_add' := fun y y' => by rw [expZ_add, map_add]
    map_smul' := fun a y => psi_aux_smul p M hpM H hHp W e a y }

theorem ψ_apply (y : L) : letI := modA p; ψ p M hpM H hHp W e y = (expZ p M hpM H hHp W e y).map (Int.castRingHom (ZMod p)) := rfl

theorem smul_top_le_ker_ψ : letI := modA p;
    (CuspForm.intIdeal p • ⊤ : Submodule A L) ≤ LinearMap.ker (ψ p M hpM H hHp W e) := by
  letI := modA p
  rw [Submodule.smul_le]
  intro r hr y _
  rw [LinearMap.mem_ker, map_smul]
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  show redA p (c * (p : A)) • ψ p M hpM H hHp W e y = 0
  have h0 : redA p (c * (p : A)) = 0 := by
    rw [map_mul, redA_apply, redA_apply, toZ_natCast, Int.cast_natCast, ZMod.natCast_self, mul_zero]
  rw [h0, zero_smul]

def φ₀add : Ω₀ →+ PowerSeries (ZMod p) :=
  letI := modA p
  (((CuspForm.intIdeal p • ⊤ : Submodule A L).liftQ (ψ p M hpM H hHp W e) (smul_top_le_ker_ψ p M hpM H hHp W e)).toAddMonoidHom :
    (L ⧸ (CuspForm.intIdeal p • ⊤ : Submodule A L)) →+ PowerSeries (ZMod p))

def φ₀ : Ω₀ →ₗ[ZMod p] PowerSeries (ZMod p) :=
  (φ₀add p M hpM H hHp W e).toZModLinearMap p

theorem φ₀_reduce (y : L) :
    φ₀ p M hpM H hHp W e (CuspForm.intTwoCuspReduce M H p y) = (expZ p M hpM H hHp W e y).map (Int.castRingHom (ZMod p)) := rfl

theorem diffQExp_ρ_tmul_reduce {ρ : K ⊗[ZMod p] Ω₀ →ₗ[K] Ω[F̄⁄K]}
    (hρ : ∀ (f : CuspForm Γ 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
      (pfW : PowerSeries ℤ), IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
        diffQExp F̄ (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) = intSeriesC K pfW) (y : L) :
    diffQExp F̄ (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y)) = intSeriesC K (expZ p M hpM H hHp W e y) := by

  suffices h : ∃ pf : PowerSeries ℤ, IsIntegralQExp ⇑(Xf p M hpM H hHp W e (y : CuspForm Γ 2)) pf ∧
      diffQExp F̄ (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y)) = intSeriesC K pf by
    obtain ⟨pf, hpf, h⟩ := h
    rw [h, (isIntegralQExp_expZ p M hpM H hHp W e y).unique hpf]
  obtain ⟨f, hf⟩ := y
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    have hc : ∀ n, ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) n ∈ A := fun n => by
      have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hfS) (CuspForm.diamondLinH 2 e)
        (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia e)) W n
      exact h.2
    have hpf' : IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) (PowerSeries.mk fun n => toZ ⟨_, hc n⟩) := by
      rw [isIntegralQExp_iff]
      intro n
      rw [PowerSeries.coeff_mk, cast_toZ]
      rfl
    have hpf : IsIntegralQExp ⇑(Xf p M hpM H hHp W e f) (PowerSeries.mk fun n => toZ ⟨_, hc n⟩) := by
      rw [coe_Xf]; exact hpf'
    exact ⟨_, hpf, hρ f hfS _ hpf'⟩
  | zero =>
    refine ⟨0, by rw [show ((⟨0, Submodule.zero_mem _⟩ : L) : CuspForm Γ 2) = 0 from rfl, Xf_zero]; simpa using isIntegralQExp_zero, ?_⟩
    have : (⟨0, Submodule.zero_mem _⟩ : L) = 0 := rfl
    rw [this, map_zero, TensorProduct.tmul_zero, map_zero, map_zero, intSeriesC_zero]
  | add f g hf' hg' hf hg =>
    obtain ⟨pf, hpf, hf⟩ := hf
    obtain ⟨pg, hpg, hg⟩ := hg
    refine ⟨pf + pg, by
      show IsIntegralQExp ⇑(Xf p M hpM H hHp W e (f + g)) (pf + pg)
      rw [Xf_add]; exact isIntegralQExp_add M H hpf hpg, ?_⟩
    have : (⟨f + g, Submodule.add_mem _ hf' hg'⟩ : L) = ⟨f, hf'⟩ + ⟨g, hg'⟩ := rfl
    rw [this, map_add, TensorProduct.tmul_add, map_add, map_add, hf, hg]
    simp [intSeriesC]
  | smul a f hf' hf =>
    obtain ⟨pf, hpf, hf⟩ := hf
    refine ⟨toZ a • pf, ?_, ?_⟩
    · have : ((⟨a • f, Submodule.smul_mem _ a hf'⟩ : L) : CuspForm Γ 2) = toZ a • f := smul_eq_toZ_zsmul a f
      rw [this, Xf_zsmul]
      exact isIntegralQExp_zsmul M H hpf (toZ a)
    · have h1 : (⟨a • f, Submodule.smul_mem _ a hf'⟩ : L) = toZ a • ⟨f, hf'⟩ := by
        apply Subtype.ext
        show a • f = ((toZ a • (⟨f, hf'⟩ : L) : L) : CuspForm Γ 2)
        rw [Submodule.coe_smul_of_tower]
        exact smul_eq_toZ_zsmul a f
      rw [h1, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p) (toZ a), TensorProduct.tmul_smul,
        ← algebraMap_smul K ((toZ a : ℤ) : ZMod p), map_smul, LinearMap.map_smul_of_tower, hf, map_intCast,
        Int.cast_smul_eq_zsmul]
      simp only [intSeriesC, map_zsmul]

include hHp in

theorem main {ρ : K ⊗[ZMod p] Ω₀ →ₗ[K] Ω[F̄⁄K]}
    (hρ : ∀ (f : CuspForm Γ 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
      (pfW : PowerSeries ℤ), IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
        diffQExp F̄ (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) = intSeriesC K pfW)
    (x : K ⊗[ZMod p] Ω₀) (hx : ρ x = 0) :
    x ∈ Submodule.span K {z : K ⊗[ZMod p] Ω₀ |
      ∃ y : L, (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff
          (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e (y : CuspForm Γ 2))) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} := by

  have hTG : ∀ z : K ⊗[ZMod p] Ω₀, diffQExp F̄ (ρ z) =
      (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) (LinearMap.lTensor K (φ₀ p M hpM H hHp W e) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      obtain ⟨y, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p m
      have hc1 : c ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y =
          c • ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.lTensor_tmul, ι_tmul, φ₀_reduce, hc1, map_smul, LinearMap.map_smul_of_tower,
        diffQExp_ρ_tmul_reduce p M hpM H K hHp W e hρ y]
      congr 1
      rw [intSeriesC, ← RingHom.comp_apply (PowerSeries.map (algebraMap (ZMod p) K))
          (PowerSeries.map (Int.castRingHom (ZMod p))) (expZ p M hpM H hHp W e y), ← PowerSeries.map_comp,
        RingHom.ext_int ((algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p))) (Int.castRingHom K)]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  have hG : (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) (LinearMap.lTensor K (φ₀ p M hpM H hHp W e) x) = 0 := by
    rw [← hTG, hx, map_zero]
  have hker : LinearMap.lTensor K (φ₀ p M hpM H hHp W e) x = 0 :=
    (ι_injective p K) (by rw [map_zero]; exact hG)

  have hexact := Module.Flat.lTensor_exact K (LinearMap.exact_subtype_ker_map (φ₀ p M hpM H hHp W e))
  obtain ⟨w, hw⟩ := (hexact x).mp hker
  rw [← hw]
  clear hw hker hG hx
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c k =>
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    obtain ⟨y, hy⟩ := CuspForm.intTwoCuspReduce_surjective M H p (k : Ω₀)
    have hc1 : c ⊗ₜ[ZMod p] (k : Ω₀) = c • ((1 : K) ⊗ₜ[ZMod p] (k : Ω₀)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc1]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨y, ?_, by rw [hy]⟩)
    intro n
    have hk : φ₀ p M hpM H hHp W e (k : Ω₀) = 0 := LinearMap.mem_ker.mp k.2
    rw [← hy, φ₀_reduce] at hk
    have hn : ((PowerSeries.coeff n (expZ p M hpM H hHp W e y) : ℤ) : ZMod p) = 0 := by
      have := congrArg (PowerSeries.coeff n) hk
      rwa [PowerSeries.coeff_map, map_zero, eq_intCast] at this
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hn
    refine ⟨m, ?_⟩
    rw [← coe_Xf p M hpM H hHp W e, ← cast_coeff_expZ p M hpM H hHp W e y n, hm]
    push_cast
    ring
  | add w₁ w₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂

end Main

end ModularCurve.LinAuxW

end

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) (e : (ZMod M)ˣ)
    (K : Type*) [Field K] [Algebra (ZMod p) K]
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (pfW : PowerSeries ℤ), ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW →
            ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
                (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
              ModularCurve.intSeriesC K pfW)
    (x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) (hx : ρ x = 0) :
    x ∈ Submodule.span K {z : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
      ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
        (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff
            (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e (y : CuspForm (CohCarrier.GammaH M H) 2))) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} :=
  ModularCurve.LinAuxW.main p M hpM H K hHp W e hρ x hx

end S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH
end P2MW
export P2MW.S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH (solution)
