-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.exists_realize_mul_deriv_realize_eq_div_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c7faacc1-e0e4-582c-b90a-56c4a067be71

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open UpperHalfPlane Filter AlgebraicCurve
open scoped MatrixGroups Topology Manifold

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary modularFunctionFieldFull laurentBaseChange exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange realize_eq_div"
namespace ComplexPlaceDictionary
p2m_export "ModularCurve.ComplexPlaceDictionary" "ramification pt ramification_pos meromorphicOrderAt_realize"
namespace RealizeDerivAux
p2m_open "ModularCurve.ComplexPlaceDictionary ModularCurve"

variable {N : ℕ}

abbrev qL {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : LaurentSeries ℂ :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

structure Pres (N : ℕ) (x : LaurentSeries ℂ) where
  k : ℤ
  g : ModularForm (CongruenceSubgroup.Gamma0 N) k
  h : ModularForm (CongruenceSubgroup.Gamma0 N) k
  h_ne : h ≠ 0
  eq : x * qL h = qL g

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem map_coe_nhdsNE (τ : ℍ) :
    Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] τ) = 𝓝[≠] (τ : ℂ) := by
  have h := isOpenEmbedding_coe.map_nhdsWithin_preimage_eq ({(τ : ℂ)}ᶜ) τ
  have hpre : ((↑) : ℍ → ℂ) ⁻¹' ({(τ : ℂ)}ᶜ : Set ℂ) = ({τ}ᶜ : Set ℍ) := by
    ext w
    simp
  rwa [hpre] at h

theorem eventually_nhdsNE_coe_iff {p : ℍ → Prop} {τ : ℍ} :
    (∀ᶠ z in 𝓝[≠] (τ : ℂ), p (ofComplex z)) ↔ ∀ᶠ w in 𝓝[≠] τ, p w := by
  rw [← map_coe_nhdsNE, Filter.eventually_map]
  simp only [ofComplex_apply]

theorem analyticAt_comp_ofComplex {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hf : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hf.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem eventually_ne_zero_ofComplex {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (f : ℍ → ℂ) (ofComplex z) ≠ 0 :=
  eventually_nhdsNE_coe_iff.mpr (eventually_ne_zero f hf τ)

theorem qL_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
  simpa [qL] using h

theorem realize_eventuallyEq {x : LaurentSeries ℂ} (P : Pres N x) (τ : ℍ) :
    (fun z : ℂ => realize N x (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z) := by
  filter_upwards [eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz
  exact ModularCurve.realize_eq_div N P.g P.h x P.eq (ofComplex z) hz

theorem meromorphicAt_realize {x : LaurentSeries ℂ} (P : Pres N x) (τ : ℍ) :
    MeromorphicAt (fun z : ℂ => realize N x (ofComplex z)) (τ : ℂ) :=
  ((analyticAt_comp_ofComplex P.g τ).meromorphicAt.div
    (analyticAt_comp_ofComplex P.h τ).meromorphicAt).congr (realize_eventuallyEq P τ).symm

theorem qL_mul {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) : qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N), PowerSeries.coe_mul]

theorem qL_add {a : ℤ} (f g : ModularForm (CongruenceSubgroup.Gamma0 N) a) :
    qL (f + g) = qL f + qL g := by
  simp only [qL, ModularForm.coe_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N), PowerSeries.coe_add]

theorem qL_one : qL (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) = 1 := by
  simp only [qL, ModularForm.qExpansion_one, PowerSeries.coe_one]

theorem qL_const (c : ℂ) :
    qL (c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [qL, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), ModularForm.qExpansion_one,
    Algebra.smul_def, mul_one, HahnSeries.algebraMap_apply']

theorem mul_ne_zero_of_ne_zero {a b : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) a)
    (g : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  intro hfg
  haveI : (𝓝[≠] UpperHalfPlane.I).NeBot := by
    have h : (Filter.map ((↑) : ℍ → ℂ) (𝓝[≠] UpperHalfPlane.I)).NeBot := by
      rw [map_coe_nhdsNE]; infer_instance
    exact Filter.NeBot.of_map h
  obtain ⟨w, hw⟩ := ((eventually_ne_zero f hf UpperHalfPlane.I).and
    (eventually_ne_zero g hg UpperHalfPlane.I)).exists
  have := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) (a + b) => (F : ℍ → ℂ) w) hfg
  simp only [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_zero, Pi.zero_apply,
    mul_eq_zero] at this
  exact this.elim hw.1 hw.2

theorem one_ne_zero' : (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) ≠ 0 := by
  intro h
  have := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) 0 => (F : ℍ → ℂ) UpperHalfPlane.I) h
  simp [ModularForm.one_coe_eq_one] at this

abbrev Pres.mul {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) : Pres N (x * y) where
  k := P.k + Q.k
  g := P.g.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

abbrev Pres.add {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) : Pres N (x + y) where
  k := P.k + Q.k
  g := P.g.mul Q.h + P.h.mul Q.g
  h := P.h.mul Q.h
  h_ne := mul_ne_zero_of_ne_zero P.h Q.h P.h_ne Q.h_ne
  eq := by
    rw [qL_add, qL_mul, qL_mul, qL_mul, ← P.eq, ← Q.eq]; ring

abbrev Pres.const (N : ℕ) (c : ℂ) : Pres N (algebraMap ℂ (LaurentSeries ℂ) c) where
  k := 0
  g := c • (1 : ModularForm (CongruenceSubgroup.Gamma0 N) 0)
  h := 1
  h_ne := one_ne_zero'
  eq := by
    rw [qL_one, mul_one, qL_const]

theorem realize_mul_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) (τ : ℍ) :
    (fun z : ℂ => realize N (x * y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => realize N x (ofComplex z) * realize N y (ofComplex z) := by
  filter_upwards [realize_eventuallyEq (P.mul Q) τ, realize_eventuallyEq P τ,
    realize_eventuallyEq Q τ] with z h1 h2 h3
  rw [h2, h3, h1]
  rw [ModularForm.coe_mul, ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, mul_div_mul_comm]

theorem realize_add_eventuallyEq {x y : LaurentSeries ℂ} (P : Pres N x) (Q : Pres N y) (τ : ℍ) :
    (fun z : ℂ => realize N (x + y) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => realize N x (ofComplex z) + realize N y (ofComplex z) := by
  filter_upwards [realize_eventuallyEq (P.add Q) τ, realize_eventuallyEq P τ,
    realize_eventuallyEq Q τ, eventually_ne_zero_ofComplex P.h P.h_ne τ,
    eventually_ne_zero_ofComplex Q.h Q.h_ne τ] with z h1 h2 h3 hP hQ
  rw [h2, h3, h1]
  rw [ModularForm.coe_add, Pi.add_apply, ModularForm.coe_mul, ModularForm.coe_mul,
    ModularForm.coe_mul, Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, div_add_div _ _ hP hQ,
    mul_comm ((P.h : ℍ → ℂ) (ofComplex z)) ((Q.g : ℍ → ℂ) (ofComplex z))]

theorem realize_const_eventuallyEq (c : ℂ) (τ : ℍ) :
    (fun z : ℂ => realize N (algebraMap ℂ (LaurentSeries ℂ) c) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun _ => c := by
  filter_upwards [realize_eventuallyEq (Pres.const N c) τ] with z h1
  rw [h1, ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one]
  simp

theorem eventually_eventuallyEq_nhds {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[𝓝[≠] τ] g) :
    ∀ᶠ z in 𝓝[≠] τ, f =ᶠ[𝓝 z] g := by
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h.eventually_nhds] with z hz hzτ
  filter_upwards [hz, eventually_ne_nhds (Set.mem_compl_singleton_iff.mp hzτ)] with w hw hwτ
  exact hw (Set.mem_compl_singleton_iff.mpr hwτ)

theorem deriv_eventuallyEq {f g : ℂ → ℂ} {τ : ℂ} (h : f =ᶠ[𝓝[≠] τ] g) :
    deriv f =ᶠ[𝓝[≠] τ] deriv g :=
  (eventually_eventuallyEq_nhds h).mono fun _ hz => hz.deriv_eq

theorem analyticAt_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (P : Place K F) {u : F} (hu : u ∈ P.toValuationSubring) :
    0 ≤ P.ord u := by
  by_cases hu0 : u = 0
  · simp [hu0]
  by_contra hlt
  push Not at hlt
  have hunit : IsUnit (⟨u, hu⟩ : P.toValuationSubring) := by
    by_contra hnu
    have hmax : (⟨u, hu⟩ : P.toValuationSubring) ∈ IsLocalRing.maximalIdeal P.toValuationSubring :=
      hnu
    have := (P.mem_maximalIdeal_iff_ord_pos hu0 hu).1 hmax
    omega
  obtain ⟨w, hw⟩ := hunit
  have h0 : P.ord u = 0 := by
    have := P.ord_coe_unit w
    rwa [hw] at this
  omega

theorem mem_of_ord_pos (P : Place K F) {u : F} (hu : 0 < P.ord u) :
    u ∈ P.toValuationSubring := by
  rcases P.toValuationSubring.mem_or_inv_mem u with h | h
  · exact h
  have h1 : 0 ≤ P.ord u⁻¹ := ord_nonneg_of_mem P h
  rw [Place.ord_inv] at h1
  omega

theorem mem_nonunits_of_ord_pos (P : Place K F) {u : F} (hu : 0 < P.ord u) :
    u ∈ P.toValuationSubring.nonunits := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hmem := mem_of_ord_pos P hu
  exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2
    ⟨hmem, (P.mem_maximalIdeal_iff_ord_pos hu0 hmem).2 hu⟩

end PlaceFacts

section Main

variable [NeZero N]

abbrev CF (N : ℕ) [NeZero N] : Type :=
  ↥(laurentBaseChange ℂ (modularFunctionFieldFull N))

def pres (x : CF N) : Pres N (x : LaurentSeries ℂ) :=
  let E := ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N
    (x : LaurentSeries ℂ) x.2
  ⟨E.choose, E.choose_spec.choose, E.choose_spec.choose_spec.choose,
    E.choose_spec.choose_spec.choose_spec.1, E.choose_spec.choose_spec.choose_spec.2⟩

abbrev rz (x : CF N) : ℂ → ℂ := fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)

theorem meromorphicAt_rz (x : CF N) (τ : ℍ) : MeromorphicAt (rz x) (τ : ℂ) :=
  meromorphicAt_realize (pres x) τ

theorem rz_mul (x y : CF N) (τ : ℍ) :
    rz (x * y) =ᶠ[𝓝[≠] (τ : ℂ)] fun z => rz x z * rz y z :=
  realize_mul_eventuallyEq (pres x) (pres y) τ

theorem rz_add (x y : CF N) (τ : ℍ) :
    rz (x + y) =ᶠ[𝓝[≠] (τ : ℂ)] fun z => rz x z + rz y z :=
  realize_add_eventuallyEq (pres x) (pres y) τ

theorem coe_algebraMap_CF (c : ℂ) :
    ((algebraMap ℂ (CF N) c : CF N) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c := rfl

theorem rz_algebraMap (c : ℂ) (τ : ℍ) :
    rz (algebraMap ℂ (CF N) c) =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => c := by
  have h := realize_const_eventuallyEq (N := N) c τ
  exact h

theorem rz_smul (c : ℂ) (x : CF N) (τ : ℍ) :
    rz (c • x) =ᶠ[𝓝[≠] (τ : ℂ)] fun z => c * rz x z := by
  rw [Algebra.smul_def]
  filter_upwards [rz_mul (algebraMap ℂ (CF N) c) x τ, rz_algebraMap (N := N) c τ] with z h1 h2
  rw [h1, h2]

theorem rz_one (τ : ℍ) : rz (1 : CF N) =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => 1 := by
  have h := rz_algebraMap (N := N) 1 τ
  rwa [map_one] at h

theorem eventually_differentiableAt_rz (x : CF N) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), DifferentiableAt ℂ (rz x) z := by
  have P := pres x
  have h1 : ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      rz x =ᶠ[𝓝 z] fun z => (P.g : ℍ → ℂ) (ofComplex z) / (P.h : ℍ → ℂ) (ofComplex z) :=
    eventually_eventuallyEq_nhds (realize_eventuallyEq P τ)
  have h2 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  filter_upwards [h1, h2, eventually_ne_zero_ofComplex P.h P.h_ne τ] with z hz him hh
  have hτ' : ((ofComplex z : ℍ) : ℂ) = z := by
    rw [ofComplex_apply_of_im_pos him]
  have hg := analyticAt_comp_ofComplex P.g (ofComplex z)
  have hh' := analyticAt_comp_ofComplex P.h (ofComplex z)
  rw [hτ'] at hg hh'
  exact (hg.div hh' hh).differentiableAt.congr_of_eventuallyEq hz

variable (N)

@[nolint unusedArguments]
def Gm (_N : ℕ) (τ : ℍ) : Type := Filter.Germ (𝓝[≠] ((τ : ℍ) : ℂ)) ℂ

scoped instance (τ : ℍ) : CommRing (Gm N τ) :=
  inferInstanceAs (CommRing (Filter.Germ (𝓝[≠] ((τ : ℍ) : ℂ)) ℂ))

def germ (τ : ℍ) (f : ℂ → ℂ) : Gm N τ := ((f : Filter.Germ (𝓝[≠] ((τ : ℍ) : ℂ)) ℂ) : Gm N τ)

variable {N}

omit [NeZero N] in
theorem germ_eq_iff {τ : ℍ} {f g : ℂ → ℂ} : germ N τ f = germ N τ g ↔ f =ᶠ[𝓝[≠] (τ : ℂ)] g :=
  Filter.Germ.coe_eq

omit [NeZero N] in
theorem germ_mul (τ : ℍ) (f g : ℂ → ℂ) : germ N τ (fun z => f z * g z) = germ N τ f * germ N τ g :=
  rfl

omit [NeZero N] in
theorem germ_add (τ : ℍ) (f g : ℂ → ℂ) : germ N τ (fun z => f z + g z) = germ N τ f + germ N τ g :=
  rfl

omit [NeZero N] in
theorem germ_sub (τ : ℍ) (f g : ℂ → ℂ) : germ N τ (fun z => f z - g z) = germ N τ f - germ N τ g :=
  rfl

omit [NeZero N] in
theorem germ_zero (τ : ℍ) : germ N τ (fun _ => (0 : ℂ)) = 0 := rfl

omit [NeZero N] in
theorem germ_one (τ : ℍ) : germ N τ (fun _ => (1 : ℂ)) = 1 := rfl

variable (N)

def φ (τ : ℍ) : CF N →+* Gm N τ where
  toFun x := germ N τ (rz x)
  map_one' := by
    rw [← germ_one, germ_eq_iff]
    exact rz_one τ
  map_mul' x y := by
    rw [← germ_mul, germ_eq_iff]
    exact rz_mul x y τ
  map_zero' := by
    rw [← germ_zero, germ_eq_iff]
    have h := rz_algebraMap (N := N) 0 τ
    rwa [map_zero] at h
  map_add' x y := by
    rw [← germ_add, germ_eq_iff]
    exact rz_add x y τ

theorem φ_apply (τ : ℍ) (x : CF N) : φ N τ x = germ N τ (rz x) := rfl

scoped instance algebraCF (τ : ℍ) : Algebra (CF N) (Gm N τ) := (φ N τ).toAlgebra

scoped instance algebraC (τ : ℍ) : Algebra ℂ (Gm N τ) := ((φ N τ).comp (algebraMap ℂ (CF N))).toAlgebra

scoped instance isScalarTower (τ : ℍ) : IsScalarTower ℂ (CF N) (Gm N τ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem smul_def_CF (τ : ℍ) (x : CF N) (m : Gm N τ) : x • m = germ N τ (rz x) * m := rfl

theorem smul_def_C (τ : ℍ) (c : ℂ) (m : Gm N τ) :
    c • m = germ N τ (rz (algebraMap ℂ (CF N) c)) * m := rfl

def δ (τ : ℍ) : Derivation ℂ (CF N) (Gm N τ) where
  toFun x := germ N τ (deriv (rz x))
  map_add' x y := by
    rw [← germ_add, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (rz_add x y τ), eventually_differentiableAt_rz x τ,
      eventually_differentiableAt_rz y τ] with z hz hx hy
    rw [hz, deriv_fun_add hx hy]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [smul_def_C, ← germ_mul, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (rz_smul c x τ), rz_algebraMap (N := N) c τ] with z h1 h2
    rw [h1, h2, deriv_const_mul_field]
  map_one_eq_zero' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← germ_zero, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (rz_one (N := N) τ)] with z hz
    rw [hz, deriv_const]
  leibniz' x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_def_CF, smul_def_CF, ← germ_mul, ← germ_mul, ← germ_add, germ_eq_iff]
    filter_upwards [deriv_eventuallyEq (rz_mul x y τ), eventually_differentiableAt_rz x τ,
      eventually_differentiableAt_rz y τ] with z hz hx hy
    rw [hz, deriv_fun_mul hx hy]
    ring

theorem δ_apply (τ : ℍ) (x : CF N) : δ N τ x = germ N τ (deriv (rz x)) := rfl

variable {N}

theorem eventuallyEq_of_smul_D_eq_smul_D (τ : ℍ) {a x c π : CF N}
    (h : a • KaehlerDifferential.D ℂ (CF N) x = c • KaehlerDifferential.D ℂ (CF N) π) :
    (fun z => rz a z * deriv (rz x) z) =ᶠ[𝓝[≠] (τ : ℂ)] fun z => rz c z * deriv (rz π) z := by
  have h' := congrArg ((δ N τ).liftKaehlerDifferential) h
  rw [map_smul, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, δ_apply, δ_apply, smul_def_CF, smul_def_CF,
    ← germ_mul, ← germ_mul, germ_eq_iff] at h'
  exact h'

theorem exists_eventuallyEq_zpow_mul (D : ComplexPlaceDictionary N) (τ : ℍ) {y : CF N}
    (hy : y ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ ≠ 0 ∧
      rz y =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z => (z - τ) ^ ((D.ramification τ : ℤ) * (D.pt τ).ord y) * g z := by
  have h := (meromorphicOrderAt_eq_int_iff (meromorphicAt_rz y τ)).mp
    (D.meromorphicOrderAt_realize τ y hy)
  simp only [smul_eq_mul] at h
  exact h

theorem mem_nonunits_of_eventuallyEq (D : ComplexPlaceDictionary N) (τ : ℍ) {y : CF N}
    {G : ℂ → ℂ} (hG : AnalyticAt ℂ G (τ : ℂ)) (hG0 : G τ = 0)
    (h : rz y =ᶠ[𝓝[≠] (τ : ℂ)] G) : (y : CF N) ∈ (D.pt τ).toValuationSubring.nonunits := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [ValuationSubring.mem_nonunits_iff, map_zero]
    exact zero_lt_one
  have h1 := D.meromorphicOrderAt_realize τ y hy
  change meromorphicOrderAt (rz y) (τ : ℂ) = _ at h1
  rw [meromorphicOrderAt_congr h, hG.meromorphicOrderAt_eq] at h1
  have h2 : analyticOrderAt G (τ : ℂ) ≠ 0 := fun h0 => (hG.analyticOrderAt_eq_zero.mp h0) hG0
  generalize ha : analyticOrderAt G (τ : ℂ) = n at h1 h2
  have hpos : 0 < (D.pt τ).ord y := by
    induction n using ENat.recTopCoe with
    | top =>
      rw [ENat.map_top] at h1
      exact absurd h1 WithTop.top_ne_coe
    | coe n =>
      rw [ENat.map_coe] at h1
      have h4 : (n : ℤ) = (D.ramification τ : ℤ) * (D.pt τ).ord y := by exact_mod_cast h1
      have hn : n ≠ 0 := by exact_mod_cast h2
      refine pos_of_mul_pos_right ?_ (Int.natCast_nonneg (D.ramification τ))
      rw [← h4]
      exact_mod_cast Nat.pos_of_ne_zero hn
  exact mem_nonunits_of_ord_pos _ hpos

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) [v.DCoordGenerates]

omit [NeZero N] in
theorem eq_differentialCoeff_smul_D (θ : Ω[F⁄K]) {ϖ : F}
    (hd : v.dCoord = KaehlerDifferential.D K F ϖ) :
    θ = v.differentialCoeff θ • KaehlerDifferential.D K F ϖ := by
  rw [← hd, v.differentialCoeff_smul_dCoord θ]

omit [NeZero N] in
theorem differentialCoeff_ne_zero {θ : Ω[F⁄K]} (hθ : θ ≠ 0) : v.differentialCoeff θ ≠ 0 := by
  intro h0
  apply hθ
  rw [← v.differentialCoeff_smul_dCoord θ, h0, zero_smul]

end Generic

omit [NeZero N] in

theorem local_form {τ : ℂ} {e : ℕ} (he : 0 < e) {k : ℤ} (hk : -1 ≤ k) {u s fc fπ : ℂ → ℂ}
    (hu : AnalyticAt ℂ u τ) (hs : AnalyticAt ℂ s τ)
    (hπnf : fπ =ᶠ[𝓝[≠] τ] fun z => (z - τ) ^ ((e : ℤ) * 1) * u z)
    (hcnf : fc =ᶠ[𝓝[≠] τ] fun z => (z - τ) ^ ((e : ℤ) * k) * s z) :
    ∃ (ρ : ℂ) (g : ℂ → ℂ), (k = -1 → ρ = s τ * u τ) ∧ (0 ≤ k → ρ = 0) ∧ AnalyticAt ℂ g τ ∧
      ∀ᶠ z in 𝓝[≠] τ, fc z * deriv fπ z = (e : ℂ) * ρ / (z - τ) + g z := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, e = d + 1 := Nat.exists_eq_succ_of_ne_zero he.ne'

  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun z => s z * (((d : ℂ) + 1) * u z + (z - τ) * deriv u z) :=
    ⟨_, rfl⟩
  have hFan : AnalyticAt ℂ F τ := by
    rw [hF]
    exact hs.mul ((analyticAt_const.mul hu).add ((analyticAt_id.sub analyticAt_const).mul hu.deriv))
  have hFτ : F τ = ((d : ℂ) + 1) * (s τ * u τ) := by
    rw [hF]
    simp only [sub_self, zero_mul, add_zero]
    ring
  have hderivπ : deriv fπ =ᶠ[𝓝[≠] τ]
      fun z => (z - τ) ^ d * (((d : ℂ) + 1) * u z + (z - τ) * deriv u z) := by
    have h1 : fπ =ᶠ[𝓝[≠] τ] fun z => (z - τ) ^ (d + 1) * u z := by
      filter_upwards [hπnf] with z hz
      rw [hz, mul_one, ← zpow_natCast]
    have h2 : ∀ᶠ z in 𝓝[≠] τ, AnalyticAt ℂ u z :=
      mem_nhdsWithin_of_mem_nhds hu.eventually_analyticAt
    filter_upwards [deriv_eventuallyEq h1, h2] with z hz huz
    have hd1 : HasDerivAt (fun w : ℂ => (w - τ) ^ (d + 1)) (((d : ℂ) + 1) * (z - τ) ^ d) z := by
      have := ((hasDerivAt_id z).sub_const τ).pow (d + 1)
      simp at this
      exact this
    rw [hz, deriv_fun_mul hd1.differentiableAt huz.differentiableAt, hd1.deriv]
    ring
  have hprod : (fun z => fc z * deriv fπ z) =ᶠ[𝓝[≠] τ]
      fun z => (z - τ) ^ (((d : ℤ) + 1) * k) * (z - τ) ^ d * F z := by
    filter_upwards [hcnf, hderivπ] with z h1 h2
    rw [h1, h2, hF]
    push_cast
    ring
  rcases (show k = -1 ∨ 0 ≤ k by omega) with rfl | hk0
  ·
    refine ⟨s τ * u τ, dslope F τ, fun _ => rfl, fun h => absurd h (by norm_num),
      analyticAt_dslope hFan, ?_⟩
    filter_upwards [hprod, self_mem_nhdsWithin] with z h2 hz
    have hzτ : z - τ ≠ 0 := sub_ne_zero.mpr hz
    rw [h2, dslope_of_ne _ hz, slope_def_field, hFτ, mul_neg_one, zpow_neg,
      zpow_add_one₀ hzτ, zpow_natCast]
    push_cast
    field_simp
    ring
  ·
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    refine ⟨0, fun z => (z - τ) ^ ((d + 1) * m) * (z - τ) ^ d * F z, fun h => absurd h (by omega),
      fun _ => rfl,
      ((((analyticAt_id.sub analyticAt_const).pow _).mul
        ((analyticAt_id.sub analyticAt_const).pow _)).mul hFan), ?_⟩
    filter_upwards [hprod] with z h2
    have hcast : (((d + 1) * m : ℕ) : ℤ) = ((d : ℤ) + 1) * (m : ℤ) := by push_cast; ring
    rw [h2, mul_zero, zero_div, zero_add, ← zpow_natCast (z - τ) ((d + 1) * m), hcast]

set_option maxHeartbeats 16000000 in

theorem main (D : ComplexPlaceDictionary N) [∀ w : Place ℂ (CF N), w.DCoordGenerates]
    (a x π : CF N) (τ : ℍ) (η : Ω[(CF N)⁄ℂ])
    (hηax : η = a • KaehlerDifferential.D ℂ (CF N) x)
    (hη : η ≠ 0) (hord : -1 ≤ (D.pt τ).ordDifferential η)
    (hπ : (D.pt τ).ord π = 1)
    (hdπ : (D.pt τ).dCoord = KaehlerDifferential.D ℂ (CF N) π) :
    ∃ (ρ : ℂ) (g : ℂ → ℂ),
      (D.pt τ).differentialCoeff η * π - algebraMap ℂ (CF N) ρ ∈
          (D.pt τ).toValuationSubring.nonunits ∧
      (ρ ≠ 0 ↔ (D.pt τ).ordDifferential η = -1) ∧
      AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        rz a z * deriv (rz x) z = (D.ramification τ : ℂ) * ρ / (z - τ) + g z := by

  have hηc : η = (D.pt τ).differentialCoeff η • KaehlerDifferential.D ℂ (CF N) π :=
    eq_differentialCoeff_smul_D (D.pt τ) η hdπ
  have hc0 : (D.pt τ).differentialCoeff η ≠ 0 := differentialCoeff_ne_zero (D.pt τ) hη
  obtain ⟨c, hc⟩ : ∃ c : CF N, (D.pt τ).differentialCoeff η = c := ⟨_, rfl⟩
  have hordc : (D.pt τ).ordDifferential η = (D.pt τ).ord c := by
    rw [Place.ordDifferential, hc]
  rw [hc] at hηc hc0
  rw [hc, hordc]
  rw [hordc] at hord
  clear hordc

  have hsplit : (D.pt τ).ord c = -1 ∨ 0 ≤ (D.pt τ).ord c := by
    rcases eq_or_lt_of_le hord with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by simpa using Int.add_one_le_iff.mpr h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ

  have hkey := eventuallyEq_of_smul_D_eq_smul_D τ (hηax.symm.trans hηc)

  obtain ⟨u, hu, hu0, hπnf⟩ := exists_eventuallyEq_zpow_mul D τ hπ0
  obtain ⟨s, hs, hs0, hcnf⟩ := exists_eventuallyEq_zpow_mul D τ hc0
  rw [hπ] at hπnf

  obtain ⟨ρ, g, hρ1, hρ2, hg, hloc⟩ := local_form (D.ramification_pos τ) hord hu hs hπnf hcnf
  refine ⟨ρ, g, ?_, ?_, hg, ?_⟩
  · rcases hsplit with hk | hk
    ·
      rw [hρ1 hk]
      apply mem_nonunits_of_eventuallyEq D τ (G := fun z => s z * u z - s τ * u τ)
        ((hs.mul hu).sub analyticAt_const) (sub_self _)
      have h1 := map_sub (φ N τ) (c * π) (algebraMap ℂ (CF N) (s τ * u τ))
      rw [map_mul (φ N τ) c π, φ_apply, φ_apply, φ_apply, φ_apply, ← germ_mul, ← germ_sub,
        germ_eq_iff] at h1
      filter_upwards [h1, hcnf, hπnf, rz_algebraMap (N := N) (s τ * u τ) τ,
        self_mem_nhdsWithin] with z h1 h2 h3 h4 hz
      have hne : ((z : ℂ) - τ) ^ (D.ramification τ : ℤ) ≠ 0 :=
        zpow_ne_zero _ (sub_ne_zero.mpr hz)
      rw [h1, h2, h3, h4, hk, mul_neg_one, zpow_neg, mul_one]
      calc ((z - ↑τ) ^ (D.ramification τ : ℤ))⁻¹ * s z * ((z - ↑τ) ^ (D.ramification τ : ℤ) * u z)
            - s τ * u τ
          = ((z - ↑τ) ^ (D.ramification τ : ℤ))⁻¹ * (z - ↑τ) ^ (D.ramification τ : ℤ)
              * (s z * u z) - s τ * u τ := by ring
        _ = s z * u z - s τ * u τ := by rw [inv_mul_cancel₀ hne, one_mul]
    ·
      rw [hρ2 hk, map_zero, sub_zero]
      apply mem_nonunits_of_ord_pos
      rw [(D.pt τ).ord_mul hc0 hπ0, hπ]
      exact Int.lt_add_one_iff.mpr hk
  · rcases hsplit with hk | hk
    · rw [hρ1 hk]
      exact iff_of_true (mul_ne_zero hs0 hu0) hk
    · rw [hρ2 hk]
      refine iff_of_false (fun h => h rfl) fun h => ?_
      rw [h] at hk
      exact absurd hk (by norm_num)
  · filter_upwards [hkey, hloc] with z h1 h2
    rw [h1, h2]

end Main

end ModularCurve.ComplexPlaceDictionary.RealizeDerivAux
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve.ComplexPlaceDictionary P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve.ComplexPlaceDictionary.RealizeDerivAux"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve.ComplexPlaceDictionary"
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve.ComplexPlaceDictionary P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.ModularCurve.ComplexPlaceDictionary.RealizeDerivAux"

open ModularCurve.ComplexPlaceDictionary.RealizeDerivAux in
theorem solution
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N)
    [∀ w : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)), w.DCoordGenerates]
    (a x π : ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) (τ : ℍ)
    (η : Ω[(ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N))⁄ℂ])
    (hηax : η = a • KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) x)
    (hη : η ≠ 0) (hord : -1 ≤ (D.pt τ).ordDifferential η)
    (hπ : (D.pt τ).ord π = 1)
    (hdπ : (D.pt τ).dCoord = KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) π) :
    ∃ (ρ : ℂ) (g : ℂ → ℂ),
      (D.pt τ).differentialCoeff η * π - algebraMap ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ρ ∈ (D.pt τ).toValuationSubring.nonunits ∧
      (ρ ≠ 0 ↔ (D.pt τ).ordDifferential η = -1) ∧
      AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        ModularCurve.realize N (a : LaurentSeries ℂ) (ofComplex z) *
            deriv (fun w : ℂ => ModularCurve.realize N (x : LaurentSeries ℂ) (ofComplex w)) z =
          (D.ramification τ : ℂ) * ρ / (z - τ) + g z :=
  main D a x π τ η hηax hη hord hπ hdπ

end S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add (solution)
