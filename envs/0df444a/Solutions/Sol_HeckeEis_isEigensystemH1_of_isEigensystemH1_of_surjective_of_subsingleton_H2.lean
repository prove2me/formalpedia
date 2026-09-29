-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5d4e0808-d4e4-5912-bbbd-25e8ff3fb58d

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LiftH1

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

@[scoped simp] theorem heckeLin_apply (z : Gamma0 N → V) : heckeLin N ℓ ρ a z = coeffHeckeFun N ℓ ρ a z := rfl

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

@[scoped simp] theorem coe_heckeZ1 (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    (heckeZ1 ha z : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

theorem unique_of_isCoeffHeckeOnH1 {T T' : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T)
    (hT' : IsCoeffHeckeOnH1 N ℓ ρ a T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨w', hw', hTw'⟩ := hT' z
  rw [hTw, hTw']
  congr 1
  exact Subtype.ext (hw.trans hw'.symm)

theorem eq_heckeH1_of_isCoeffHeckeOnH1 (ha : IsCompat N ℓ ρ a) {T : coeffH1 ρ →ₗ[K] coeffH1 ρ}
    (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) : T = heckeH1 ha :=
  unique_of_isCoeffHeckeOnH1 hT (isCoeffHeckeOnH1_heckeH1 ha)

theorem coeffH1Mk_eq_iff (z w : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = coeffH1Mk ρ w ↔ (z : Gamma0 N → V) - w ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.eq _).trans Submodule.mem_comap

end Induced

section Comm

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {N : ℕ} {ρ : Representation K (Gamma0 N) V}

theorem heckeH1_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (hne : ℓ ≠ ℓ') {a a' : V →ₗ[K] V}
    (ha : IsCompat N ℓ ρ a) (ha' : IsCompat N ℓ' ρ a') (hcomm : a ∘ₗ a' = a' ∘ₗ a) (x : coeffH1 ρ) :
    heckeH1 ha (heckeH1 ha' x) = heckeH1 ha' (heckeH1 ha x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [heckeH1_mk, heckeH1_mk, heckeH1_mk, heckeH1_mk, coeffH1Mk_eq_iff]
  simp only [coe_heckeZ1]
  haveI : NeZero (ℓ * ℓ') := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  have hℓℓ' : ¬ ℓ ∣ ℓ' := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp h)
  have hℓ'ℓ : ¬ ℓ' ∣ ℓ := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ' hℓ).mp h).symm
  have h1 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ ℓ' (ℓ * ℓ')
    hℓ hℓN hℓℓ' rfl ρ a a' ha ha' z.2
  have h2 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ' ℓ (ℓ * ℓ')
    hℓ' hℓ'N hℓ'ℓ (Nat.mul_comm ℓ ℓ') ρ a' a ha' ha z.2
  rw [← hcomm] at h2
  have h3 := (coeffCoboundaries ρ).sub_mem h1 h2
  convert h3 using 1
  abel

end Comm

section Functorial

variable {K : Type*} [CommRing K]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable (N : ℕ) (ρV : Representation K (Gamma0 N) V) (ρW : Representation K (Gamma0 N) W)
variable (f : V →ₗ[K] W) (hf : ∀ g : Gamma0 N, f ∘ₗ ρV g = ρW g ∘ₗ f)

include hf in
theorem f_ρ (g : Gamma0 N) (v : V) : f (ρV g v) = ρW g (f v) :=
  LinearMap.congr_fun (hf g) v

include hf in
theorem comp_mem_coeffCocycles {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρV) :
    (f ∘ z) ∈ coeffCocycles ρW := by
  intro g h
  simp only [Function.comp_apply, hz g h, map_add, f_ρ N ρV ρW f hf]

def Z1map : ↥(coeffCocycles ρV) →ₗ[K] ↥(coeffCocycles ρW) where
  toFun z := ⟨f ∘ (z : Gamma0 N → V), comp_mem_coeffCocycles N ρV ρW f hf z.2⟩
  map_add' z w := by ext g; simp
  map_smul' c z := by ext g; simp

@[scoped simp] theorem coe_Z1map (z : ↥(coeffCocycles ρV)) :
    (Z1map N ρV ρW f hf z : Gamma0 N → W) = f ∘ (z : Gamma0 N → V) := rfl

theorem comap_le_comap_Z1map :
    (coeffCoboundaries ρV).comap (coeffCocycles ρV).subtype ≤
      ((coeffCoboundaries ρW).comap (coeffCocycles ρW).subtype).comap (Z1map N ρV ρW f hf) := by
  intro z hz
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff ρV _).mp hz
  change f ∘ (z : Gamma0 N → V) ∈ coeffCoboundaries ρW
  refine (mem_coeffCoboundaries_iff ρW _).mpr ⟨f v, ?_⟩
  ext g
  have hvg := congrFun hv g
  change ρV g v - v = (z : Gamma0 N → V) g at hvg
  change ρW g (f v) - f v = f ((z : Gamma0 N → V) g)
  rw [← hvg, map_sub, f_ρ N ρV ρW f hf]

def H1map : coeffH1 ρV →ₗ[K] coeffH1 ρW :=
  ((coeffCoboundaries ρV).comap (coeffCocycles ρV).subtype).mapQ
    ((coeffCoboundaries ρW).comap (coeffCocycles ρW).subtype) (Z1map N ρV ρW f hf)
    (comap_le_comap_Z1map N ρV ρW f hf)

theorem H1map_mk (z : ↥(coeffCocycles ρV)) :
    H1map N ρV ρW f hf (coeffH1Mk ρV z) = coeffH1Mk ρW (Z1map N ρV ρW f hf z) := rfl

variable (aV : V →ₗ[K] V) (aW : W →ₗ[K] W) (hfa : f ∘ₗ aV = aW ∘ₗ f)

include hf hfa in

theorem comp_coeffHeckeFun (ℓ : ℕ) [NeZero ℓ] (z : Gamma0 N → V) :
    f ∘ coeffHeckeFun N ℓ ρV aV z = coeffHeckeFun N ℓ ρW aW (f ∘ z) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  simp only [Function.comp_apply, coeffHeckeFun_apply, map_sum, f_ρ N ρV ρW f hf]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  exact LinearMap.congr_fun hfa _

include hfa in

theorem H1map_heckeH1 (ℓ : ℕ) [NeZero ℓ] (haV : IsCompat N ℓ ρV aV) (haW : IsCompat N ℓ ρW aW)
    (x : coeffH1 ρV) :
    H1map N ρV ρW f hf (heckeH1 haV x) = heckeH1 haW (H1map N ρV ρW f hf x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρV x
  rw [heckeH1_mk, H1map_mk, H1map_mk, heckeH1_mk]
  congr 1
  refine Subtype.ext ?_
  rw [coe_Z1map, coe_heckeZ1, coe_heckeZ1, coe_Z1map, comp_coeffHeckeFun N ρV ρW f hf aV aW hfa]

end Functorial

section FiniteDim

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cocycle_apply_eq_zero_of_closure {G : Type*} [Group G] (ρ : Representation K G V)
    (z : ↥(coeffCocycles ρ)) (S : Set G) (hS : ∀ s ∈ S, (z : G → V) s = 0)
    (g : G) (hg : g ∈ Subgroup.closure S) : (z : G → V) g = 0 := by
  have hz := z.2
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    have h := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h

    have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  | mul x y _ _ ihx ihy => rw [hz x y, ihx, ihy, map_zero, zero_add]
  | inv x _ ih =>
    have h := hz x x⁻¹
    have h1 : (z : G → V) 1 = 0 := by
      have h' := hz 1 1
      rw [mul_one, map_one, Module.End.one_apply] at h'
      have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h'.symm
      exact add_left_cancel this
    rw [mul_inv_cancel, h1, ih, zero_add] at h

    have h2 : ρ x⁻¹ (ρ x ((z : G → V) x⁻¹)) = 0 := by rw [← h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

theorem finiteDimensional_coeffH1 (N : ℕ) [NeZero N] [FiniteDimensional K V]
    (ρ : Representation K (Gamma0 N) V) : FiniteDimensional K (coeffH1 ρ) := by

  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
      Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  obtain ⟨S, hS⟩ := hΓ.out

  let ev : ↥(coeffCocycles ρ) →ₗ[K] (↥S → V) :=
    { toFun := fun z s => (z : Gamma0 N → V) s
      map_add' := fun z w => by ext s; rfl
      map_smul' := fun c z => by ext s; rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    refine Subtype.ext (funext fun g => ?_)
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    exact cocycle_apply_eq_zero_of_closure ρ z S (fun s hs => congrFun hz ⟨s, hs⟩) g hg
  haveI : FiniteDimensional K ↥(coeffCocycles ρ) := Module.Finite.of_injective ev hev
  exact Module.Finite.of_surjective (coeffH1Mk ρ) (coeffH1Mk_surjective ρ)

end FiniteDim

section LinAlg

variable {F : Type*} [Field F]

theorem coe_restrict_pow {M : Type*} [AddCommGroup M] [Module F M] (f : M →ₗ[F] M)
    (P : Submodule F M) (h : ∀ v ∈ P, f v ∈ P) (k : ℕ) (v : ↥P) :
    (((f.restrict h) ^ k) v : M) = (f ^ k) (v : M) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem exists_common_ker_of_nilpotent : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) → Nontrivial M →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT hnil hM hd
  by_cases hz : ∀ i, T i = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact ⟨v, hv, fun i => by rw [hz i, LinearMap.zero_apply]⟩
  push_neg at hz
  obtain ⟨i₀, hi₀⟩ := hz
  set P : Submodule F M := LinearMap.ker (T i₀) with hP
  have hPtop : P ≠ ⊤ := fun h => hi₀ (LinearMap.ker_eq_top.mp h)
  have hPbot : P ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (T i₀) := LinearMap.ker_eq_bot.mp h
    obtain ⟨k, hk⟩ := hnil i₀
    have hinjk : Function.Injective ((T i₀) ^ k) := by
      rw [Module.End.coe_pow]; exact Function.Injective.iterate hinj k
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact hv (hinjk (by rw [hk, map_zero, LinearMap.zero_apply]))
  have hstab : ∀ i, ∀ v ∈ P, T i v ∈ P := by
    intro i v hv
    rw [hP, LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, (hT i₀ i).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P →ₗ[F] ↥P := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hnil' : ∀ i, IsNilpotent (T' i) := by
    intro i
    obtain ⟨k, hk⟩ := hnil i
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    change ((((T i).restrict (hstab i)) ^ k) v : M) = ((0 : ↥P →ₗ[F] ↥P) v : M)
    rw [coe_restrict_pow, hk]
    rfl
  haveI : Nontrivial ↥P := Submodule.nontrivial_iff_ne_bot.mpr hPbot
  have hlt : Module.finrank F ↥P < d := hd ▸ Submodule.finrank_lt hPtop
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' hnil' inferInstance rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_ker_of_range_le : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → ∀ (P : Submodule F M), P ≠ ⊤ → (∀ i x, T i x ∈ P) →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT P hP hTP hd
  by_cases hall : ∀ i, IsNilpotent (T i)
  ·
    have hex : ∃ v : M, v ∉ P := by
      by_contra h
      push_neg at h
      exact hP (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hv⟩ := hex
    have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
    haveI : Nontrivial M := nontrivial_of_ne v 0 hv0
    exact exists_common_ker_of_nilpotent d T hT hall inferInstance hd
  push_neg at hall
  obtain ⟨i₀, hi₀⟩ := hall
  set f := T i₀ with hf

  obtain ⟨k, hk, hk1⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and (Filter.eventually_ge_atTop 1)).exists
  set P' : Submodule F M := LinearMap.ker (f ^ k) with hP'
  set Q : Submodule F M := LinearMap.range (f ^ k) with hQ
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hi₀
    exact ⟨k, LinearMap.range_eq_bot.mp h⟩
  have hP'top : P' ≠ ⊤ := by
    intro h
    have hdis := hk.disjoint
    rw [h] at hdis
    exact hQbot (top_disjoint.mp hdis)

  have hQP : Q ≤ P := by
    rintro _ ⟨x, rfl⟩
    have hfk : f ^ k = f * f ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
    rw [hfk, Module.End.mul_apply]
    exact hTP i₀ _

  have hP'P : P.comap P'.subtype ≠ ⊤ := by
    intro h
    have hle : P' ≤ P := fun v hv => by
      have : (⟨v, hv⟩ : ↥P') ∈ P.comap P'.subtype := by rw [h]; trivial
      exact this
    apply hP
    rw [eq_top_iff, ← hk.codisjoint.eq_top]
    exact sup_le hle hQP

  have hstab : ∀ i, ∀ v ∈ P', T i v ∈ P' := by
    intro i v hv
    rw [hP', LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ((hT i₀ i).pow_left k).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P' →ₗ[F] ↥P' := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hTP' : ∀ i (x : ↥P'), T' i x ∈ P.comap P'.subtype := fun i x => hTP i (x : M)
  have hlt : Module.finrank F ↥P' < d := hd ▸ Submodule.finrank_lt hP'top
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' (P.comap P'.subtype) hP'P hTP' rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_eigenvector {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {ι : Type*} (T : ι → M →ₗ[F] M) (hT : ∀ i j, Commute (T i) (T j)) (c : ι → F)
    (P : Submodule F M) (hP : P ≠ ⊤) (hTP : ∀ i x, T i x - c i • x ∈ P) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = c i • v := by
  let T' : ι → M →ₗ[F] M := fun i => T i - c i • 1
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    refine Commute.sub_left (Commute.sub_right (hT i j) ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.refl (1 : M →ₗ[F] M)).smul_right _).smul_left _
  have hTP' : ∀ i x, T' i x ∈ P := fun i x => by
    simpa [T', LinearMap.sub_apply, LinearMap.smul_apply] using hTP i x
  obtain ⟨v, hv, hTv⟩ := exists_common_ker_of_range_le _ T' hT' P hP hTP' rfl
  refine ⟨v, hv, fun i => ?_⟩
  have := hTv i
  simp only [T', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

end LinAlg

section Systems

def Good (N : ℕ) (S₀ : Set ℕ) (ℓ : ℕ) : Prop := ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀

theorem Good.neZero {N : ℕ} {S₀ : Set ℕ} {ℓ : ℕ} (h : Good N S₀ ℓ) : NeZero ℓ := ⟨h.1.ne_zero⟩

variable {K : Type*} [Field K] {N : ℕ} (S₀ : Set ℕ)
variable {V : Type*} [AddCommGroup V] [Module K V]

def GoodCompat (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V)) : Prop :=
  ∀ (ℓ : ℕ) (h : Good N S₀ ℓ), @IsCompat K _ V _ _ N ℓ h.neZero ρ (a ℓ)

noncomputable def Tgood {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (ℓ : ℕ) (h : Good N S₀ ℓ) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  @heckeH1 K _ V _ _ N ℓ h.neZero ρ (a ℓ) (hc ℓ h)

def IsEigvec {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (lam : ℕ → K) (x : coeffH1 ρ) : Prop :=
  ∀ (ℓ : ℕ) (h : Good N S₀ ℓ), Tgood S₀ hc ℓ h x = lam ℓ • x

def GoodCommute {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) : Prop :=
  ∀ (ℓ ℓ' : ℕ) (h : Good N S₀ ℓ) (h' : Good N S₀ ℓ'), Commute (Tgood S₀ hc ℓ h) (Tgood S₀ hc ℓ' h')

theorem isEigensystemH1_iff {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (lam : ℕ → K) :
    IsEigensystemH1 N ρ a S₀ lam ↔ ∃ x : coeffH1 ρ, x ≠ 0 ∧ IsEigvec S₀ hc lam x := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun ℓ hg => ?_⟩
    obtain ⟨T, hT, hTx⟩ := h ℓ hg.1 hg.2.1 hg.2.2
    haveI : NeZero ℓ := hg.neZero
    have hT' : IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T := hT
    rw [eq_heckeH1_of_isCoeffHeckeOnH1 (hc ℓ hg) hT'] at hTx
    exact hTx
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ⟨Tgood S₀ hc ℓ ⟨hℓ, hℓN, hℓS⟩, isCoeffHeckeOnH1_heckeH1 _, h ℓ ⟨hℓ, hℓN, hℓS⟩⟩

theorem goodCommute_of_comm {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (hcomm : ∀ ℓ ℓ', Good N S₀ ℓ → Good N S₀ ℓ' → a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ) :
    GoodCommute S₀ hc := by
  intro ℓ ℓ' h h'
  by_cases hne : ℓ = ℓ'
  · subst hne
    exact Commute.refl _
  refine LinearMap.ext fun x => ?_
  haveI := h.neZero
  haveI := h'.neZero
  exact heckeH1_comm h.1 h'.1 h.2.1 h'.2.1 hne (hc ℓ h) (hc ℓ' h') (hcomm ℓ ℓ' h h') x

section Transport

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {ρV : Representation K (Gamma0 N) V} {aV : ℕ → (V →ₗ[K] V)} (hcV : GoodCompat S₀ ρV aV)
variable {ρW : Representation K (Gamma0 N) W} {aW : ℕ → (W →ₗ[K] W)} (hcW : GoodCompat S₀ ρW aW)
variable (f : V →ₗ[K] W) (hf : ∀ g : Gamma0 N, f ∘ₗ ρV g = ρW g ∘ₗ f)
  (hfa : ∀ ℓ, Good N S₀ ℓ → f ∘ₗ aV ℓ = aW ℓ ∘ₗ f)

include hfa in
theorem H1map_Tgood (ℓ : ℕ) (h : Good N S₀ ℓ) (x : coeffH1 ρV) :
    H1map N ρV ρW f hf (Tgood S₀ hcV ℓ h x) = Tgood S₀ hcW ℓ h (H1map N ρV ρW f hf x) := by
  haveI := h.neZero
  exact H1map_heckeH1 N ρV ρW f hf (aV ℓ) (aW ℓ) (hfa ℓ h) ℓ (hcV ℓ h) (hcW ℓ h) x

include hfa in
theorem isEigvec_H1map {lam : ℕ → K} {x : coeffH1 ρV} (hx : IsEigvec S₀ hcV lam x) :
    IsEigvec S₀ hcW lam (H1map N ρV ρW f hf x) := by
  intro ℓ h
  rw [← H1map_Tgood S₀ hcV hcW f hf hfa ℓ h, hx ℓ h, map_smul]

end Transport

end Systems

end LiftH1
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

namespace LiftH1

open CategoryTheory CategoryTheory.Limits CongruenceSubgroup HeckeEis groupCohomology
open scoped MatrixGroups

section Surj

variable {κ : Type} [CommRing κ] {V V'' : Type} [AddCommGroup V] [Module κ V] [AddCommGroup V''] [Module κ V'']
variable (N : ℕ) (ρ : Representation κ (Gamma0 N) V) (ρ'' : Representation κ (Gamma0 N) V'')
variable (π : V →ₗ[κ] V'') (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)

noncomputable abbrev A : Rep κ (Gamma0 N) := Rep.of ρ
noncomputable abbrev B : Rep κ (Gamma0 N) := Rep.of ρ''

private noncomputable def _root_.LiftH1.f : A N ρ ⟶ B N ρ'' :=
  Rep.ofHom
    { toLinearMap := π
      isIntertwining' := fun g => hπ g }

p2m_export "LiftH1" "f"
theorem f_hom_apply (v : V) : (f N ρ ρ'' π hπ).hom v = π v := rfl

private theorem _root_.LiftH1.epi_f (hsurj : Function.Surjective π) : Epi (f N ρ ρ'' π hπ) := by
  rw [Rep.epi_iff_surjective]
  exact hsurj

p2m_export "LiftH1" "epi_f"

noncomputable def X : ShortComplex (Rep κ (Gamma0 N)) :=
  ShortComplex.mk (kernel.ι (f N ρ ρ'' π hπ)) (f N ρ ρ'' π hπ) (kernel.condition _)

theorem X_shortExact (hsurj : Function.Surjective π) : (X N ρ ρ'' π hπ).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (f N ρ ρ'' π hπ))
  mono_f := by dsimp [X]; infer_instance
  epi_g := epi_f N ρ ρ'' π hπ hsurj

theorem map_f_surjective (hsurj : Function.Surjective π)
    (hH2 : ∀ A : Rep κ ↥(Gamma0 N), Subsingleton (groupCohomology A 2)) :
    Function.Surjective ((groupCohomology.functor κ (Gamma0 N) 1).map (f N ρ ρ'' π hπ)) := by
  have hX := X_shortExact N ρ ρ'' π hπ hsurj
  have hexact := groupCohomology.mapShortComplex₃_exact hX (i := 1) (j := 2) rfl
  haveI : Subsingleton (groupCohomology (X N ρ ρ'' π hπ).X₁ 2) := hH2 _
  have hzero : IsZero (groupCohomology (X N ρ ρ'' π hπ).X₁ 2) := ModuleCat.isZero_of_subsingleton _
  have hg : (groupCohomology.mapShortComplex₃ hX (i := 1) (j := 2) rfl).g = 0 := hzero.eq_of_tgt _ _
  have hepi : Epi (groupCohomology.mapShortComplex₃ hX (i := 1) (j := 2) rfl).f := hexact.epi_f hg
  have hepi' : Epi ((groupCohomology.functor κ (Gamma0 N) 1).map (f N ρ ρ'' π hπ)) := hepi
  exact (ModuleCat.epi_iff_surjective _).mp hepi'

theorem mem_cocycles₁_B (z'' : ↥(coeffCocycles ρ'')) : ((z'' : Gamma0 N → V'')) ∈ cocycles₁ (B N ρ'') := by
  rw [mem_cocycles₁_iff]
  intro g h
  change (z'' : Gamma0 N → V'') (g * h) = ρ'' g ((z'' : Gamma0 N → V'') h) + (z'' : Gamma0 N → V'') g
  rw [z''.2 g h, add_comm]

theorem mem_coeffCocycles_A (z : cocycles₁ (A N ρ)) : (⇑z : Gamma0 N → V) ∈ coeffCocycles ρ := by
  intro g h
  have := (mem_cocycles₁_iff (A := A N ρ) z).mp z.2 g h
  rw [this, add_comm]

theorem H1map_surjective (hsurj : Function.Surjective π)
    (hH2 : ∀ A : Rep κ ↥(Gamma0 N), Subsingleton (groupCohomology A 2)) :
    Function.Surjective (H1map N ρ ρ'' π hπ) := by
  intro y
  obtain ⟨z'', rfl⟩ := coeffH1Mk_surjective ρ'' y
  let zB : cocycles₁ (B N ρ'') := ⟨_, mem_cocycles₁_B N ρ'' z''⟩
  obtain ⟨yA, hyA⟩ := map_f_surjective N ρ ρ'' π hπ hsurj hH2 (H1π (B N ρ'') zB)
  obtain ⟨zA, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π (A N ρ))).mp inferInstance yA
  rw [groupCohomology.functor_map] at hyA
  have key := H1π_comp_map_apply (A := A N ρ) (B := B N ρ'') (MonoidHom.id _) (f N ρ ρ'' π hπ) zA
  have hy3 : H1π (B N ρ'') (mapCocycles₁ (MonoidHom.id (Gamma0 N)) (f N ρ ρ'' π hπ) zA)
      = H1π (B N ρ'') zB := key.symm.trans hyA
  rw [H1π_eq_iff] at hy3
  obtain ⟨v3, hv3⟩ := hy3
  refine ⟨coeffH1Mk ρ ⟨⇑zA, mem_coeffCocycles_A N ρ zA⟩, ?_⟩
  rw [H1map_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  change ((π ∘ (⇑zA : Gamma0 N → V)) - (z'' : Gamma0 N → V'')) ∈ coeffCoboundaries ρ''
  refine (mem_coeffCoboundaries_iff ρ'' _).mpr ⟨v3, funext fun g => ?_⟩
  have hg := congrFun hv3 g
  exact hg

include hπ in

theorem exists_cocycle_lift (hsurj : Function.Surjective π)
    (hH2 : ∀ A : Rep κ ↥(Gamma0 N), Subsingleton (groupCohomology A 2)) (z'' : ↥(coeffCocycles ρ'')) :
    ∃ w : ↥(coeffCocycles ρ), π ∘ (w : Gamma0 N → V) = (z'' : Gamma0 N → V'') := by
  obtain ⟨y, hy⟩ := H1map_surjective N ρ ρ'' π hπ hsurj hH2 (coeffH1Mk ρ'' z'')
  obtain ⟨w₀, rfl⟩ := coeffH1Mk_surjective ρ y
  rw [H1map_mk, coeffH1Mk_eq_iff] at hy
  obtain ⟨v'', hv''⟩ := (mem_coeffCoboundaries_iff ρ'' _).mp hy
  obtain ⟨v, rfl⟩ := hsurj v''
  have hcob : (fun g => ρ g v - v) ∈ coeffCocycles ρ :=
    coeffCoboundaries_le_coeffCocycles ρ ((mem_coeffCoboundaries_iff ρ _).mpr ⟨v, rfl⟩)
  refine ⟨w₀ - ⟨fun g => ρ g v - v, hcob⟩, funext fun g => ?_⟩
  have hg := congrFun hv'' g
  change ρ'' g (π v) - π v = π ((w₀ : Gamma0 N → V) g) - (z'' : Gamma0 N → V'') g at hg
  change π ((w₀ : Gamma0 N → V) g - (ρ g v - v)) = (z'' : Gamma0 N → V'') g
  rw [map_sub, map_sub, f_ρ N ρ ρ'' π hπ, hg]
  abel

end Surj
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

end LiftH1
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

namespace LiftH1

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Lift

variable (N ℓ₀ : ℕ) [NeZero ℓ₀]

theorem gamma0_mul_le : Gamma0 (N * ℓ₀) ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have h : ((N * ℓ₀ : ℕ) : ℤ) ∣ (A 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast hA)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_trans (by exact_mod_cast Dvd.intro ℓ₀ rfl) h

def incl : Gamma0 (N * ℓ₀) →* Gamma0 N := Subgroup.inclusion (gamma0_mul_le N ℓ₀)

@[scoped simp] theorem coe_incl (g : Gamma0 (N * ℓ₀)) : ((incl N ℓ₀ g : Gamma0 N) : SL(2, ℤ)) = (g : SL(2, ℤ)) := rfl

theorem heckeConj_mem (t : ↥(heckeUpper N ℓ₀)) :
    ((heckeConj N ℓ₀ t : Gamma0 N) : SL(2, ℤ)) ∈ Gamma0 (N * ℓ₀) := by
  rw [Gamma0_mem]
  have hc : (((( t : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp (t : Gamma0 N).2
  have hN : (N : ℤ) ∣ (((t : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have h10 : (((heckeConj N ℓ₀ t : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) = (((t : Gamma0 N) : SL(2, ℤ)) 1 0 : ℤ) * ℓ₀ := by
    rw [coe_heckeConj, show ((heckeConjSL N ℓ₀ t) 1 0 : ℤ) = (heckeConjSL N ℓ₀ t : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl,
      coe_heckeConjSL, heckeConjMat_apply_one_zero]
  rw [h10, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact mul_dvd_mul_right hN _

def conj' (t : ↥(heckeUpper N ℓ₀)) : Gamma0 (N * ℓ₀) :=
  ⟨((heckeConj N ℓ₀ t : Gamma0 N) : SL(2, ℤ)), heckeConj_mem N ℓ₀ t⟩

@[scoped simp] theorem incl_conj' (t : ↥(heckeUpper N ℓ₀)) : incl N ℓ₀ (conj' N ℓ₀ t) = heckeConj N ℓ₀ t := rfl

theorem conj'_mul (t t' : ↥(heckeUpper N ℓ₀)) : conj' N ℓ₀ (t * t') = conj' N ℓ₀ t * conj' N ℓ₀ t' := by
  apply Subtype.ext
  change ((heckeConj N ℓ₀ (t * t') : Gamma0 N) : SL(2, ℤ)) = _
  rw [map_mul]
  rfl

variable {κ : Type} [CommRing κ] {V V'' : Type} [AddCommGroup V] [Module κ V] [AddCommGroup V''] [Module κ V'']
variable (ρ : Representation κ (Gamma0 N) V) (a : V →ₗ[κ] V)

noncomputable def liftFun (w : Gamma0 (N * ℓ₀) → V) : Gamma0 N → V :=
  fun g =>
    letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ₀,
      ρ (g • q).out (a (w (conj' N ℓ₀ (transferAux (heckeUpper N ℓ₀) g q))))

theorem liftFun_apply (w : Gamma0 (N * ℓ₀) → V) (g : Gamma0 N) :
    liftFun N ℓ₀ ρ a w g =
      letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
      ∑ q : Gamma0 N ⧸ heckeUpper N ℓ₀,
        ρ (g • q).out (a (w (conj' N ℓ₀ (transferAux (heckeUpper N ℓ₀) g q)))) := rfl

theorem liftFun_comp_incl (z : Gamma0 N → V) :
    liftFun N ℓ₀ ρ a (z ∘ incl N ℓ₀) = coeffHeckeFun N ℓ₀ ρ a z := by
  funext g
  rw [liftFun_apply, coeffHeckeFun_apply]
  rfl

variable {ρ a}

theorem liftFun_mem_coeffCocycles (ha : IsCompat N ℓ₀ ρ a) {w : Gamma0 (N * ℓ₀) → V}
    (hw : w ∈ coeffCocycles (ρ.comp (incl N ℓ₀))) :
    liftFun N ℓ₀ ρ a w ∈ coeffCocycles ρ := by
  letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
  intro g h
  simp only [liftFun_apply]
  have ha_apply : ∀ (u : ↥(heckeUpper N ℓ₀)) (v : V), a (ρ (heckeConj N ℓ₀ u) v) = ρ (u : Gamma0 N) (a v) :=
    fun u v => by simpa using LinearMap.congr_fun (ha u) v
  have out_mul : ∀ (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ₀),
      (g • q).out * (transferAux (heckeUpper N ℓ₀) g q : Gamma0 N) = g * q.out := fun g q => by
    rw [coe_transferAux, mul_inv_cancel_left]
  have key : ∀ q : Gamma0 N ⧸ heckeUpper N ℓ₀,
      ρ ((g * h) • q).out (a (w (conj' N ℓ₀ (transferAux (heckeUpper N ℓ₀) (g * h) q))))
        = ρ (g • (h • q)).out (a (w (conj' N ℓ₀ (transferAux (heckeUpper N ℓ₀) g (h • q)))))
          + ρ g (ρ (h • q).out (a (w (conj' N ℓ₀ (transferAux (heckeUpper N ℓ₀) h q))))) := by
    intro q
    rw [transferAux_mul, conj'_mul, hw, map_add, map_add, mul_smul]
    congr 1
    rw [MonoidHom.comp_apply, incl_conj', ha_apply, ← Module.End.mul_apply, ← map_mul, out_mul, map_mul,
      Module.End.mul_apply]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, map_sum]
  congr 1
  exact Fintype.sum_bijective (h • ·) (MulAction.bijective h) _ _ fun q => rfl

variable (ρ'' : Representation κ (Gamma0 N) V'') (a'' : V'' →ₗ[κ] V'') (π : V →ₗ[κ] V'')

theorem comp_liftFun (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π) (hπa : π ∘ₗ a = a'' ∘ₗ π)
    (w : Gamma0 (N * ℓ₀) → V) (z : Gamma0 N → V'') (hwz : π ∘ w = z ∘ incl N ℓ₀) :
    π ∘ liftFun N ℓ₀ ρ a w = coeffHeckeFun N ℓ₀ ρ'' a'' z := by
  letI := (heckeUpper N ℓ₀).fintypeQuotientOfFiniteIndex
  funext g
  simp only [Function.comp_apply, liftFun_apply, coeffHeckeFun_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h1 := congrFun hwz (conj' N ℓ₀ (transferAux (heckeUpper N ℓ₀) g q))
  simp only [Function.comp_apply, incl_conj'] at h1
  rw [f_ρ N ρ ρ'' π hπ, show π (a _) = a'' (π _) from LinearMap.congr_fun hπa _, h1]

end Lift
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

end LiftH1
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

namespace LiftH1

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Pull

variable {κ : Type} [Field κ] {V V'' : Type} [AddCommGroup V] [Module κ V] [AddCommGroup V''] [Module κ V'']

theorem main (N : ℕ) [NeZero N] (S₀ : Set ℕ) [FiniteDimensional κ V]
    (ρ : Representation κ (Gamma0 N) V) (ρ'' : Representation κ (Gamma0 N) V'')
    (a : ℕ → (V →ₗ[κ] V)) (a'' : ℕ → (V'' →ₗ[κ] V''))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(heckeUpper N ℓ), a ℓ ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a ℓ)
    (hcomm : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ∉ S₀ →
      a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (π : V →ₗ[κ] V'') (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
    (hπa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)
    (hsurj : Function.Surjective π)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀S : ℓ₀ ∉ S₀)
    (hH2 : ∀ A : Rep κ ↥(Gamma0 (N * ℓ₀)), Subsingleton (groupCohomology A 2))
    (lam : ℕ → κ) (hlam : lam ℓ₀ ≠ 0)
    (h : IsEigensystemH1 N ρ'' a'' S₀ lam) : IsEigensystemH1 N ρ a S₀ lam := by

  have hcV : GoodCompat S₀ ρ a := fun ℓ hg => by
    haveI := hg.neZero
    exact ha ℓ hg.1 hg.2.1 hg.2.2
  have hcW : GoodCompat S₀ ρ'' a'' := by
    intro ℓ hg
    haveI := hg.neZero
    intro u
    refine LinearMap.ext fun v'' => ?_
    obtain ⟨v, rfl⟩ := hsurj v''
    have e1 : a'' ℓ (ρ'' (heckeConj N ℓ u) (π v)) = π (a ℓ (ρ (heckeConj N ℓ u) v)) := by
      rw [← f_ρ N ρ ρ'' π hπ, show π (a ℓ _) = a'' ℓ (π _) from
        LinearMap.congr_fun (hπa ℓ hg.1 hg.2.1 hg.2.2) _]
    have e2 : ρ'' (u : Gamma0 N) (a'' ℓ (π v)) = π (ρ (u : Gamma0 N) (a ℓ v)) := by
      rw [← show π (a ℓ _) = a'' ℓ (π _) from LinearMap.congr_fun (hπa ℓ hg.1 hg.2.1 hg.2.2) _,
        f_ρ N ρ ρ'' π hπ]
    change a'' ℓ (ρ'' (heckeConj N ℓ u) (π v)) = ρ'' (u : Gamma0 N) (a'' ℓ (π v))
    rw [e1, e2]
    exact congrArg π (LinearMap.congr_fun (ha ℓ hg.1 hg.2.1 hg.2.2 u) v)
  have hfa : ∀ ℓ, Good N S₀ ℓ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π := fun ℓ hg => hπa ℓ hg.1 hg.2.1 hg.2.2
  have hcommV : GoodCommute S₀ hcV :=
    goodCommute_of_comm S₀ hcV fun ℓ ℓ' hg hg' => hcomm ℓ ℓ' hg.1 hg.2.1 hg.2.2 hg'.1 hg'.2.1 hg'.2.2
  haveI : FiniteDimensional κ (coeffH1 ρ) := finiteDimensional_coeffH1 N ρ

  obtain ⟨x, hx, heig⟩ := (isEigensystemH1_iff S₀ hcW lam).mp h

  have hg₀ : Good N S₀ ℓ₀ := ⟨hℓ₀, hℓ₀N, hℓ₀S⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : coeffH1 ρ, H1map N ρ ρ'' π hπ y₀ = x := by
    haveI : NeZero ℓ₀ := hg₀.neZero
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ'' x

    let ρr : Representation κ (Gamma0 (N * ℓ₀)) V := ρ.comp (incl N ℓ₀)
    let ρr'' : Representation κ (Gamma0 (N * ℓ₀)) V'' := ρ''.comp (incl N ℓ₀)
    have hπr : ∀ g : Gamma0 (N * ℓ₀), π ∘ₗ ρr g = ρr'' g ∘ₗ π := fun g => hπ (incl N ℓ₀ g)
    have hzr : ((z : Gamma0 N → V'') ∘ incl N ℓ₀) ∈ coeffCocycles ρr'' := fun g h => by
      simp only [Function.comp_apply, map_mul]
      exact z.2 _ _
    obtain ⟨w, hw⟩ := exists_cocycle_lift (N * ℓ₀) ρr ρr'' π hπr hsurj hH2 ⟨_, hzr⟩

    have hW : liftFun N ℓ₀ ρ (a ℓ₀) (w : Gamma0 (N * ℓ₀) → V) ∈ coeffCocycles ρ :=
      liftFun_mem_coeffCocycles N ℓ₀ (hcV ℓ₀ hg₀) w.2
    have hπW : π ∘ liftFun N ℓ₀ ρ (a ℓ₀) (w : Gamma0 (N * ℓ₀) → V) =
        coeffHeckeFun N ℓ₀ ρ'' (a'' ℓ₀) (z : Gamma0 N → V'') :=
      comp_liftFun N ℓ₀ ρ'' (a'' ℓ₀) π hπ (hfa ℓ₀ hg₀) w z hw
    have hTz : H1map N ρ ρ'' π hπ (coeffH1Mk ρ ⟨_, hW⟩) = lam ℓ₀ • coeffH1Mk ρ'' z := by
      rw [← heig ℓ₀ hg₀, H1map_mk]
      change coeffH1Mk ρ'' (Z1map N ρ ρ'' π hπ ⟨_, hW⟩) = coeffH1Mk ρ'' (heckeZ1 (hcW ℓ₀ hg₀) z)
      congr 1
      exact Subtype.ext hπW
    refine ⟨(lam ℓ₀)⁻¹ • coeffH1Mk ρ ⟨_, hW⟩, ?_⟩
    rw [map_smul, hTz, smul_smul, inv_mul_cancel₀ hlam, one_smul]

  let M : Submodule κ (coeffH1 ρ) := (Submodule.span κ {x}).comap (H1map N ρ ρ'' π hπ)
  have hfx : ∀ m ∈ M, ∃ r : κ, r • x = H1map N ρ ρ'' π hπ m := fun m hm =>
    Submodule.mem_span_singleton.mp hm
  have hstabM : ∀ ℓ (hg : Good N S₀ ℓ), ∀ m ∈ M, Tgood S₀ hcV ℓ hg m ∈ M := by
    intro ℓ hg m hm
    obtain ⟨r, hr⟩ := hfx m hm
    change H1map N ρ ρ'' π hπ (Tgood S₀ hcV ℓ hg m) ∈ Submodule.span κ {x}
    rw [H1map_Tgood S₀ hcV hcW π hπ hfa ℓ hg, ← hr, map_smul, heig ℓ hg, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  let ι := {ℓ : ℕ // Good N S₀ ℓ}
  let TM : ι → ↥M →ₗ[κ] ↥M := fun ℓ => (Tgood S₀ hcV ℓ.1 ℓ.2).restrict (hstabM ℓ.1 ℓ.2)
  have hTM : ∀ u v : ι, Commute (TM u) (TM v) := fun u v =>
    LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hcommV u.1 v.1 u.2 v.2).eq (m : coeffH1 ρ))
  let P : Submodule κ ↥M := (LinearMap.ker (H1map N ρ ρ'' π hπ)).comap M.subtype
  have hy₀M : y₀ ∈ M := by
    change H1map N ρ ρ'' π hπ y₀ ∈ Submodule.span κ {x}
    rw [hy₀]; exact Submodule.mem_span_singleton_self x
  have hP : P ≠ ⊤ := by
    intro hP
    have : (⟨y₀, hy₀M⟩ : ↥M) ∈ P := by rw [hP]; trivial
    change H1map N ρ ρ'' π hπ y₀ = 0 at this
    rw [hy₀] at this
    exact hx this
  have hTP : ∀ (u : ι) (m : ↥M), TM u m - lam u.1 • m ∈ P := by
    intro u m
    obtain ⟨r, hr⟩ := hfx m m.2
    change H1map N ρ ρ'' π hπ (Tgood S₀ hcV u.1 u.2 m - lam u.1 • (m : coeffH1 ρ)) = 0
    rw [map_sub, map_smul, H1map_Tgood S₀ hcV hcW π hπ hfa u.1 u.2, ← hr, map_smul, heig u.1 u.2,
      smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨v, hv, hTv⟩ := exists_common_eigenvector TM hTM (fun u => lam u.1) P hP hTP
  refine (isEigensystemH1_iff S₀ hcV lam).mpr ⟨(v : coeffH1 ρ), fun h0 => hv (Subtype.ext h0), fun ℓ hg => ?_⟩
  exact congrArg Subtype.val (hTv ⟨ℓ, hg⟩)

end Pull
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

end LiftH1
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2.LiftH1"

open scoped MatrixGroups in
theorem solution
    (N : ℕ) [NeZero N] {κ : Type} [Field κ] (S₀ : Set ℕ)
    {V V'' : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] [AddCommGroup V''] [Module κ V'']
    (ρ : Representation κ (CongruenceSubgroup.Gamma0 N) V) (ρ'' : Representation κ (CongruenceSubgroup.Gamma0 N) V'')
    (a : ℕ → (V →ₗ[κ] V)) (a'' : ℕ → (V'' →ₗ[κ] V''))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (hcomm : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ∉ S₀ →
      a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (π : V →ₗ[κ] V'') (hπ : ∀ g : CongruenceSubgroup.Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
    (hπa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)
    (hsurj : Function.Surjective π)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀S : ℓ₀ ∉ S₀)
    (hH2 : ∀ A : Rep κ ↥(CongruenceSubgroup.Gamma0 (N * ℓ₀)), Subsingleton (groupCohomology A 2))
    (lam : ℕ → κ) (hlam : lam ℓ₀ ≠ 0) (h : HeckeEis.IsEigensystemH1 N ρ'' a'' S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam :=
  LiftH1.main N S₀ ρ ρ'' a a'' ha hcomm π hπ hπa hsurj ℓ₀ hℓ₀ hℓ₀N hℓ₀S hH2 lam hlam h

end S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2 (solution)
