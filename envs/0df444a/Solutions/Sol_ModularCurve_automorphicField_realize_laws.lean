-- Prove2me | solution 1 for ModularCurve.automorphicField_realize_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/521978c2-2479-5ae3-9908-f4e059d74670

import Mathlib
import Definitions.Def_ModularCurve_AutomorphicField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_automorphicField_realize_laws

set_option autoImplicit false

noncomputable section

open Filter UpperHalfPlane ModularCurve
open scoped MatrixGroups Topology Manifold

namespace T5inv

variable {Γ : Subgroup (GL (Fin 2) ℝ)}

theorem eventually_ne_zero_of_mem_holRing {s : ℍ → ℂ} (hs : s ∈ holRing) (hs0 : s ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, s z ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ z in 𝓝[≠] τ, s z = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hs0 (UpperHalfPlane.eq_zero_of_frequently hs hfr)

theorem tendsto_smul_nhdsNE (γ : GL (Fin 2) ℝ) (τ : ℍ) :
    Tendsto (fun z : ℍ => γ • z) (𝓝[≠] τ) (𝓝[≠] (γ • τ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact ((continuous_const_smul γ).tendsto τ).mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun z hz => ?_
    intro h
    exact hz (smul_left_cancel γ h)

variable [Γ.HasDetOne]

theorem realize_eventuallyEq_div (x : ↥(automorphicField Γ)) {k : ℤ} {g h : ModularForm Γ k}
    (hh : (h : ℍ → ℂ) ≠ 0)
    (hx : (x : FractionRing ↥holRing) =
      algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
        algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing)
    (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, automorphicField.realize x z = (g : ℍ → ℂ) z / (h : ℍ → ℂ) z := by
  set p := IsLocalization.sec (nonZeroDivisors ↥holRing) (x : FractionRing ↥holRing) with hp
  have hspec : (x : FractionRing ↥holRing) * algebraMap (↥holRing) (FractionRing ↥holRing) (p.2 : ↥holRing) =
      algebraMap (↥holRing) (FractionRing ↥holRing) p.1 :=
    IsLocalization.sec_spec (nonZeroDivisors ↥holRing) (x : FractionRing ↥holRing)

  have hs0 : ((p.2 : ↥holRing) : ℍ → ℂ) ≠ 0 := by
    intro h0
    have : (p.2 : ↥holRing) = 0 := Subtype.ext h0
    exact (nonZeroDivisors.ne_zero p.2.prop) this
  have hhalg : algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing ≠ 0 := by
    intro h0
    apply hh
    have : h.toHolRing = 0 :=
      (IsFractionRing.injective (↥holRing) (FractionRing ↥holRing)) (by rw [h0, RingHom.map_zero])
    exact (ModularForm.toHolRing_eq_zero_iff h).1 this

  have hcross : g.toHolRing * (p.2 : ↥holRing) = p.1 * h.toHolRing := by
    apply IsFractionRing.injective (↥holRing) (FractionRing ↥holRing)
    rw [map_mul, map_mul, ← hspec]
    have hg : algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing =
        (x : FractionRing ↥holRing) * algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing := by
      rw [hx, div_mul_cancel₀ _ hhalg]
    rw [hg, mul_right_comm]
  have hcrossz : ∀ z : ℍ, (g : ℍ → ℂ) z * ((p.2 : ↥holRing) : ℍ → ℂ) z =
      ((p.1 : ↥holRing) : ℍ → ℂ) z * (h : ℍ → ℂ) z := by
    intro z
    have := congrArg (fun f : ↥holRing => (f : ℍ → ℂ) z) hcross
    simpa using this
  filter_upwards [eventually_ne_zero_of_mem_holRing (p.2 : ↥holRing).prop hs0 τ,
    eventually_ne_zero_of_mem_holRing h.holo' hh τ] with z hsz hhz
  have hhz' : (h : ℍ → ℂ) z ≠ 0 := hhz
  rw [automorphicField.realize_def, merRealize_apply, ← hp, div_eq_div_iff hsz hhz']
  exact (hcrossz z).symm

theorem realize_smul_eventuallyEq (x : ↥(automorphicField Γ)) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (τ : ℍ) : ∀ᶠ z in 𝓝[≠] τ, automorphicField.realize x (γ • z) = automorphicField.realize x z := by
  obtain ⟨k, g, h, hh, hx⟩ := (mem_automorphicField_iff (x : FractionRing ↥holRing)).1 x.prop
  have h1 := realize_eventuallyEq_div x hh hx τ
  have h2 : ∀ᶠ z in 𝓝[≠] τ, automorphicField.realize x (γ • z) = (g : ℍ → ℂ) (γ • z) / (h : ℍ → ℂ) (γ • z) :=
    (tendsto_smul_nhdsNE γ τ).eventually (realize_eventuallyEq_div x hh hx (γ • τ))
  have h3 : ∀ᶠ z in 𝓝[≠] τ, (h : ℍ → ℂ) z ≠ 0 := eventually_ne_zero_of_mem_holRing h.holo' hh τ
  filter_upwards [h1, h2, h3] with z h1z h2z h3z
  rw [h2z, h1z, SlashInvariantForm.slash_action_eqn'' g hγ z, SlashInvariantForm.slash_action_eqn'' h hγ z,
    mul_div_mul_left _ _ (zpow_ne_zero k (denom_ne_zero γ z))]

end T5inv

namespace T1laws

theorem analyticAt_comp_ofComplex (f : ↥ModularCurve.holRing) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.2).analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem meromorphicAt_merRealize (x : FractionRing ↥ModularCurve.holRing) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => merRealize x (ofComplex z)) (τ : ℂ) := by
  have e : (fun z : ℂ => merRealize x (ofComplex z)) =
      fun z : ℂ => ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).1 : ℍ → ℂ) (ofComplex z) /
        (((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing) : ℍ → ℂ) (ofComplex z) := rfl
  rw [e]
  exact (analyticAt_comp_ofComplex _ τ).meromorphicAt.div (analyticAt_comp_ofComplex _ τ).meromorphicAt

theorem sec_snd_ne_zero (x : FractionRing ↥ModularCurve.holRing) :
    ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero _

private theorem _root_.T1laws.coe_ne_zero {s : ↥ModularCurve.holRing} (hs : s ≠ 0) : (s : ℍ → ℂ) ≠ 0 :=
  fun h0 => hs (Subtype.ext h0)

p2m_export "T1laws" "coe_ne_zero"
theorem eq_sec_div (x : FractionRing ↥ModularCurve.holRing) :
    x = algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).1 /
      algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing) := by
  rw [eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing))).mpr (sec_snd_ne_zero x))]
  exact (IsLocalization.sec_spec (nonZeroDivisors ↥ModularCurve.holRing) x)

theorem mul_eq_mul_of_div_eq_div {g h g' h' : ↥ModularCurve.holRing} (hh : h ≠ 0) (hh' : h' ≠ 0)
    (e : algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) g / algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) h =
      algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) g' / algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) h') :
    g * h' = g' * h := by
  have hinj := IsFractionRing.injective ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing)
  rw [div_eq_div_iff ((map_ne_zero_iff _ hinj).mpr hh) ((map_ne_zero_iff _ hinj).mpr hh'),
    ← map_mul, ← map_mul] at e
  exact hinj e

theorem merRealize_eventuallyEq_div (x : FractionRing ↥ModularCurve.holRing) (g h : ↥ModularCurve.holRing) (hh : h ≠ 0)
    (hx : x = algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) g / algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) h) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, merRealize x z = (g : ℍ → ℂ) z / (h : ℍ → ℂ) z := by
  set a := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).1 with ha
  set s : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing) with hs
  have hs0 : s ≠ 0 := sec_snd_ne_zero x
  have hrel : a * h = g * s := mul_eq_mul_of_div_eq_div hs0 hh ((eq_sec_div x).symm.trans hx)
  have hpt : ∀ w : ℍ, (a : ℍ → ℂ) w * (h : ℍ → ℂ) w = (g : ℍ → ℂ) w * (s : ℍ → ℂ) w := fun w => by
    have := congrArg (fun f : ↥ModularCurve.holRing => (f : ℍ → ℂ) w) hrel
    simpa using this
  filter_upwards [T5inv.eventually_ne_zero_of_mem_holRing h.2 (coe_ne_zero hh) τ,
    T5inv.eventually_ne_zero_of_mem_holRing s.2 (coe_ne_zero hs0) τ] with z hz hsz
  rw [merRealize_apply, div_eq_div_iff hsz hz]
  exact hpt z

theorem merRealize_add_eventuallyEq (x y : FractionRing ↥ModularCurve.holRing) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, merRealize (x + y) z = merRealize x z + merRealize y z := by
  set a₁ := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).1
  set s₁ : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing)
  set a₂ := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) y).1
  set s₂ : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) y).2 : ↥ModularCurve.holRing)
  have hs₁ : s₁ ≠ 0 := sec_snd_ne_zero x
  have hs₂ : s₂ ≠ 0 := sec_snd_ne_zero y
  have hinj := IsFractionRing.injective ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing)
  set φ := algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) with hφ
  have H1 : φ s₁ ≠ 0 := (map_ne_zero_iff φ hinj).mpr hs₁
  have H2 : φ s₂ ≠ 0 := (map_ne_zero_iff φ hinj).mpr hs₂
  have hxy : x + y = φ (a₁ * s₂ + s₁ * a₂) / φ (s₁ * s₂) := by
    conv_lhs => rw [eq_sec_div x, eq_sec_div y]
    rw [RingHom.map_add φ, RingHom.map_mul φ, RingHom.map_mul φ, RingHom.map_mul φ, div_add_div _ _ H1 H2]
  filter_upwards [merRealize_eventuallyEq_div (x + y) _ (s₁ * s₂) (mul_ne_zero hs₁ hs₂) hxy τ,
    T5inv.eventually_ne_zero_of_mem_holRing s₁.2 (coe_ne_zero hs₁) τ,
    T5inv.eventually_ne_zero_of_mem_holRing s₂.2 (coe_ne_zero hs₂) τ] with z hz h1 h2
  rw [hz, merRealize_apply, merRealize_apply, div_add_div _ _ h1 h2]
  rfl

theorem merRealize_mul_eventuallyEq (x y : FractionRing ↥ModularCurve.holRing) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, merRealize (x * y) z = merRealize x z * merRealize y z := by
  set a₁ := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).1
  set s₁ : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing)
  set a₂ := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) y).1
  set s₂ : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) y).2 : ↥ModularCurve.holRing)
  have hs₁ : s₁ ≠ 0 := sec_snd_ne_zero x
  have hs₂ : s₂ ≠ 0 := sec_snd_ne_zero y
  have hxy : x * y = algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) (a₁ * a₂) / algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) (s₁ * s₂) := by
    conv_lhs => rw [eq_sec_div x, eq_sec_div y]
    rw [map_mul, map_mul, div_mul_div_comm]
  filter_upwards [merRealize_eventuallyEq_div (x * y) (a₁ * a₂) (s₁ * s₂) (mul_ne_zero hs₁ hs₂) hxy τ] with z hz
  rw [hz, merRealize_apply, merRealize_apply, div_mul_div_comm]
  rfl

theorem merRealize_algebraMap_eventuallyEq (c : ℂ) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] τ, merRealize (algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) (algebraMap ℂ ↥ModularCurve.holRing c)) z = c := by
  have hx : algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) (algebraMap ℂ ↥ModularCurve.holRing c) =
      algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) (algebraMap ℂ ↥ModularCurve.holRing c) / algebraMap ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing) 1 := by
    rw [map_one, div_one]
  filter_upwards [merRealize_eventuallyEq_div _ _ 1 one_ne_zero hx τ] with z hz
  rw [hz]
  simp [Algebra.algebraMap_eq_smul_one]

theorem eq_of_eventuallyEq (x y : FractionRing ↥ModularCurve.holRing) (τ : ℍ)
    (h : ∀ᶠ z in 𝓝[≠] τ, merRealize x z = merRealize y z) : x = y := by
  set a := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).1 with ha
  set s : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) x).2 : ↥ModularCurve.holRing) with hs
  set a' := (IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) y).1 with ha'
  set s' : ↥ModularCurve.holRing := ((IsLocalization.sec (nonZeroDivisors ↥ModularCurve.holRing) y).2 : ↥ModularCurve.holRing) with hs'
  have hs0 : s ≠ 0 := sec_snd_ne_zero x
  have hs0' : s' ≠ 0 := sec_snd_ne_zero y

  have hev : ∀ᶠ z in 𝓝[≠] τ, ((a * s' - a' * s : ↥ModularCurve.holRing) : ℍ → ℂ) z = 0 := by
    filter_upwards [h, T5inv.eventually_ne_zero_of_mem_holRing s.2 (coe_ne_zero hs0) τ,
      T5inv.eventually_ne_zero_of_mem_holRing s'.2 (coe_ne_zero hs0') τ] with z hz h1 h2
    rw [merRealize_apply, merRealize_apply, div_eq_div_iff h1 h2] at hz
    change (a : ℍ → ℂ) z * (s' : ℍ → ℂ) z - (a' : ℍ → ℂ) z * (s : ℍ → ℂ) z = 0
    rw [hz, sub_self]
  have hzero : (a * s' - a' * s : ↥ModularCurve.holRing) = 0 := by
    apply Subtype.ext
    exact UpperHalfPlane.eq_zero_of_frequently (a * s' - a' * s).2 hev.frequently
  have hrel : a * s' = a' * s := sub_eq_zero.mp hzero
  have hinj := IsFractionRing.injective ↥ModularCurve.holRing (FractionRing ↥ModularCurve.holRing)
  rw [eq_sec_div x, eq_sec_div y,
    div_eq_div_iff ((map_ne_zero_iff _ hinj).mpr hs0) ((map_ne_zero_iff _ hinj).mpr hs0'),
    ← map_mul, ← map_mul]
  exact congrArg _ hrel

end T1laws

end

open Filter UpperHalfPlane ModularCurve in
open scoped MatrixGroups Topology Manifold in
theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] :

    (∀ (a s : ↥ModularCurve.holRing), s ≠ 0 → ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.merRealize
          (algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) a /
            algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) s) z =
        (a : ℍ → ℂ) z / (s : ℍ → ℂ) z) ∧
    (∀ (x : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ),
      MeromorphicAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ)) ∧
    (∀ (x y : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (x + y) z =
        ModularCurve.automorphicField.realize x z + ModularCurve.automorphicField.realize y z) ∧
    (∀ (x y : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (x * y) z =
        ModularCurve.automorphicField.realize x z * ModularCurve.automorphicField.realize y z) ∧
    (∀ (c : ℂ) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (algebraMap ℂ ↥(ModularCurve.automorphicField Γ) c) z = c) ∧
    (∀ x y : ↥(ModularCurve.automorphicField Γ),
      (∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
        ModularCurve.automorphicField.realize x z = ModularCurve.automorphicField.realize y z) → x = y) ∧
    (∀ (x : ↥(ModularCurve.automorphicField Γ)), ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize x (γ • z) = ModularCurve.automorphicField.realize x z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a s hs τ
    exact T1laws.merRealize_eventuallyEq_div _ a s hs rfl τ
  · intro x τ
    exact T1laws.meromorphicAt_merRealize _ τ
  · intro x y τ
    exact T1laws.merRealize_add_eventuallyEq _ _ τ
  · intro x y τ
    exact T1laws.merRealize_mul_eventuallyEq _ _ τ
  · intro c τ
    exact T1laws.merRealize_algebraMap_eventuallyEq c τ
  · intro x y hxy
    apply Subtype.ext
    exact T1laws.eq_of_eventuallyEq _ _ UpperHalfPlane.I (hxy UpperHalfPlane.I)
  · intro x γ hγ τ
    exact T5inv.realize_smul_eventuallyEq x hγ τ

end S_ModularCurve_automorphicField_realize_laws
end P2MW
export P2MW.S_ModularCurve_automorphicField_realize_laws (solution)
