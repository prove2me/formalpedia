-- Prove2me | solution 1 for HeckeEis.exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ebf2188b-0989-5e8e-a974-3e45e93d6ac4

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_Gamma0NebenRep
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd

set_option autoImplicit false

namespace ASF

open CongruenceSubgroup HeckeEis MvPolynomial
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

section Twist

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ : Representation K (Gamma0 N) V)

theorem coeffHeckeFun_smul (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V) (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ (c • a) z = c • coeffHeckeFun N ℓ ρ a z := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  simp only [coeffHeckeFun_apply, Pi.smul_apply, LinearMap.smul_apply, map_smul, Finset.smul_sum]

theorem smul_isCoeffHeckeOnH1 (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V)
    {T : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) :
    IsCoeffHeckeOnH1 N ℓ ρ (c • a) (c • T) := by
  intro z
  obtain ⟨w, hw, hTw⟩ := hT z
  refine ⟨c • w, ?_, ?_⟩
  · rw [Submodule.coe_smul, hw, coeffHeckeFun_smul]
  · rw [LinearMap.smul_apply, hTw, map_smul]

theorem isEigensystemH1_of_smul (a a' : ℕ → (V →ₗ[K] V)) (χ : ℕ → K) (S₀ : Set ℕ) (lam : ℕ → K)
    (haa' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a' ℓ = χ ℓ • a ℓ)
    (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a' S₀ (fun ℓ => χ ℓ * lam ℓ) := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨χ ℓ • T, ?_, ?_⟩
  · have := smul_isCoeffHeckeOnH1 N ρ ℓ (χ ℓ) (a ℓ) hT
    rw [← haa' ℓ hℓ hℓN hℓS] at this
    exact this
  · rw [LinearMap.smul_apply, hTx, smul_smul]

theorem isEigensystemH1_of_smul_of_mul_eq_one (a a' : ℕ → (V →ₗ[K] V)) (χ χ' : ℕ → K) (S₀ : Set ℕ)
    (lam : ℕ → K) (haa' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a' ℓ = χ ℓ • a ℓ)
    (hunit : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → χ' ℓ * χ ℓ = 1)
    (h : IsEigensystemH1 N ρ a' S₀ lam) :
    IsEigensystemH1 N ρ a S₀ (fun ℓ => χ' ℓ * lam ℓ) :=
  isEigensystemH1_of_smul N ρ a' a χ' S₀ lam
    (fun ℓ hℓ hℓN hℓS => by rw [haa' ℓ hℓ hℓN hℓS, smul_smul, hunit ℓ hℓ hℓN hℓS, one_smul]) h

end Twist

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

section Exact

variable {K : Type*} [CommRing K]
variable {V' V V'' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]
  [AddCommGroup V''] [Module K V'']
variable (N : ℕ) (ρ' : Representation K (Gamma0 N) V') (ρ : Representation K (Gamma0 N) V)
  (ρ'' : Representation K (Gamma0 N) V'')
variable (i : V' →ₗ[K] V) (hi : ∀ g : Gamma0 N, i ∘ₗ ρ' g = ρ g ∘ₗ i)
variable (π : V →ₗ[K] V'') (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)

include hi hπ in

theorem exists_H1map_eq_of_H1map_eq_zero (hinj : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker π) (hsurj : Function.Surjective π) (x : coeffH1 ρ)
    (hx : H1map N ρ ρ'' π hπ x = 0) :
    ∃ y : coeffH1 ρ', H1map N ρ' ρ i hi y = x := by
  obtain ⟨c, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [H1map_mk, coeffH1Mk_eq_zero_iff] at hx
  change (π ∘ (c : Gamma0 N → V)) ∈ coeffCoboundaries ρ'' at hx
  obtain ⟨w'', hw''⟩ := (mem_coeffCoboundaries_iff ρ'' _).mp hx
  obtain ⟨w, rfl⟩ := hsurj w''
  have hval : ∀ g : Gamma0 N, (c : Gamma0 N → V) g - coeffCoboundaryMap ρ w g ∈ LinearMap.range i := by
    intro g
    rw [hexact, LinearMap.mem_ker, map_sub]
    have h1 := congrFun hw'' g
    simp only [Function.comp_apply] at h1
    rw [← h1, coeffCoboundaryMap_apply, map_sub, f_ρ N ρ ρ'' π hπ, sub_self]
  choose d hd using hval
  have hdc : (fun g => i (d g)) = (c : Gamma0 N → V) - coeffCoboundaryMap ρ w := funext hd
  have hd_mem : d ∈ coeffCocycles ρ' := by
    intro g h
    apply hinj
    rw [map_add, f_ρ N ρ' ρ i hi, hd, hd, hd]
    have hc2 := (c.2 : (c : Gamma0 N → V) ∈ coeffCocycles ρ) g h
    have hb2 := coeffCoboundaries_le_coeffCocycles ρ (LinearMap.mem_range_self _ w) g h
    simp only [hc2, hb2, map_sub, coeffCoboundaryMap_apply]
    abel
  refine ⟨coeffH1Mk ρ' ⟨d, hd_mem⟩, ?_⟩
  rw [H1map_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  change ((fun g => i (d g)) - (c : Gamma0 N → V)) ∈ coeffCoboundaries ρ
  rw [hdc, sub_sub_cancel_left]
  exact (coeffCoboundaries ρ).neg_mem (LinearMap.mem_range_self _ _)

end Exact

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

section Step

variable {V' V'' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable {ρ' : Representation K (Gamma0 N) V'} {a' : ℕ → (V' →ₗ[K] V')} (hc' : GoodCompat S₀ ρ' a')
variable {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)} (hc : GoodCompat S₀ ρ a)
variable {ρ'' : Representation K (Gamma0 N) V''} {a'' : ℕ → (V'' →ₗ[K] V'')} (hc'' : GoodCompat S₀ ρ'' a'')
variable (i : V' →ₗ[K] V) (hi : ∀ g : Gamma0 N, i ∘ₗ ρ' g = ρ g ∘ₗ i)
  (hia : ∀ ℓ, Good N S₀ ℓ → i ∘ₗ a' ℓ = a ℓ ∘ₗ i)
variable (π : V →ₗ[K] V'') (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
  (hπa : ∀ ℓ, Good N S₀ ℓ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)

include hi hia hπ hπa in

theorem step [FiniteDimensional K (coeffH1 ρ')] (hcomm' : GoodCommute S₀ hc')
    (hinj : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker π)
    (hsurj : Function.Surjective π) (lam : ℕ → K) (x : coeffH1 ρ) (hx : x ≠ 0)
    (heig : IsEigvec S₀ hc lam x) :
    (∃ y : coeffH1 ρ'', y ≠ 0 ∧ IsEigvec S₀ hc'' lam y) ∨
      (∃ y : coeffH1 ρ', y ≠ 0 ∧ IsEigvec S₀ hc' lam y) := by
  by_cases hzero : H1map N ρ ρ'' π hπ x = 0
  swap
  · exact Or.inl ⟨_, hzero, isEigvec_H1map S₀ hc hc'' π hπ hπa heig⟩
  right
  obtain ⟨y₀, hy₀⟩ := exists_H1map_eq_of_H1map_eq_zero N ρ' ρ ρ'' i hi π hπ hinj hexact hsurj x hzero

  let M : Submodule K (coeffH1 ρ') := (Submodule.span K {x}).comap (H1map N ρ' ρ i hi)
  have hfx : ∀ m ∈ M, ∃ r : K, r • x = H1map N ρ' ρ i hi m := fun m hm =>
    Submodule.mem_span_singleton.mp hm
  have hstabM : ∀ ℓ (h : Good N S₀ ℓ), ∀ m ∈ M, Tgood S₀ hc' ℓ h m ∈ M := by
    intro ℓ h m hm
    obtain ⟨r, hr⟩ := hfx m hm
    change H1map N ρ' ρ i hi (Tgood S₀ hc' ℓ h m) ∈ Submodule.span K {x}
    rw [H1map_Tgood S₀ hc' hc i hi hia ℓ h, ← hr, map_smul, heig ℓ h, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  let ι := {ℓ : ℕ // Good N S₀ ℓ}
  let TM : ι → ↥M →ₗ[K] ↥M := fun ℓ => (Tgood S₀ hc' ℓ.1 ℓ.2).restrict (hstabM ℓ.1 ℓ.2)
  have hTM : ∀ u v : ι, Commute (TM u) (TM v) := fun u v =>
    LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hcomm' u.1 v.1 u.2 v.2).eq (m : coeffH1 ρ'))
  let P : Submodule K ↥M := (LinearMap.ker (H1map N ρ' ρ i hi)).comap M.subtype
  have hy₀M : y₀ ∈ M := by
    change H1map N ρ' ρ i hi y₀ ∈ Submodule.span K {x}
    rw [hy₀]; exact Submodule.mem_span_singleton_self x
  have hP : P ≠ ⊤ := by
    intro h
    have : (⟨y₀, hy₀M⟩ : ↥M) ∈ P := by rw [h]; trivial
    change H1map N ρ' ρ i hi y₀ = 0 at this
    rw [hy₀] at this
    exact hx this
  have hTP : ∀ (u : ι) (m : ↥M), TM u m - lam u.1 • m ∈ P := by
    intro u m
    obtain ⟨r, hr⟩ := hfx m m.2
    change H1map N ρ' ρ i hi (Tgood S₀ hc' u.1 u.2 m - lam u.1 • (m : coeffH1 ρ')) = 0
    rw [map_sub, map_smul, H1map_Tgood S₀ hc' hc i hi hia u.1 u.2, ← hr, map_smul, heig u.1 u.2,
      smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨v, hv, hTv⟩ := exists_common_eigenvector TM hTM (fun u => lam u.1) P hP hTP
  refine ⟨(v : coeffH1 ρ'), fun h => hv (Subtype.ext h), fun ℓ h => ?_⟩
  exact congrArg Subtype.val (hTv ⟨ℓ, h⟩)

end Step

section Sub

variable (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V))
variable (W : Submodule K V) (hρW : ∀ g : Gamma0 N, ∀ v ∈ W, ρ g v ∈ W)
  (haW : ∀ ℓ, Good N S₀ ℓ → ∀ v ∈ W, a ℓ v ∈ W)

def subRep : Representation K (Gamma0 N) ↥W where
  toFun g := (ρ g).restrict (hρW g)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by simp)

@[scoped simp] theorem coe_subRep_apply (g : Gamma0 N) (v : ↥W) :
    ((subRep ρ W hρW g v : ↥W) : V) = ρ g v := rfl

open Classical in

noncomputable def subFam : ℕ → (↥W →ₗ[K] ↥W) := fun ℓ =>
  if h : Good N S₀ ℓ then (a ℓ).restrict (haW ℓ h) else 0

theorem subFam_of_good {ℓ : ℕ} (h : Good N S₀ ℓ) :
    subFam S₀ a W haW ℓ = (a ℓ).restrict (haW ℓ h) := by
  simp [subFam, h]

@[scoped simp] theorem coe_subFam_apply {ℓ : ℕ} (h : Good N S₀ ℓ) (v : ↥W) :
    ((subFam S₀ a W haW ℓ v : ↥W) : V) = a ℓ v := by
  rw [subFam_of_good S₀ a W haW h]; rfl

theorem goodCompat_sub (hc : GoodCompat S₀ ρ a) : GoodCompat S₀ (subRep ρ W hρW) (subFam S₀ a W haW) := by
  intro ℓ h u
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ((subFam S₀ a W haW ℓ (subRep ρ W hρW _ v) : ↥W) : V) =
    ((subRep ρ W hρW _ (subFam S₀ a W haW ℓ v) : ↥W) : V)
  rw [coe_subFam_apply S₀ a W haW h, coe_subRep_apply, coe_subRep_apply, coe_subFam_apply S₀ a W haW h]
  exact LinearMap.congr_fun (hc ℓ h u) (v : V)

theorem sub_comm (hcomm : ∀ ℓ ℓ', Good N S₀ ℓ → Good N S₀ ℓ' → a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (ℓ ℓ' : ℕ) (h : Good N S₀ ℓ) (h' : Good N S₀ ℓ') :
    subFam S₀ a W haW ℓ ∘ₗ subFam S₀ a W haW ℓ' = subFam S₀ a W haW ℓ' ∘ₗ subFam S₀ a W haW ℓ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ((subFam S₀ a W haW ℓ (subFam S₀ a W haW ℓ' v) : ↥W) : V) =
    ((subFam S₀ a W haW ℓ' (subFam S₀ a W haW ℓ v) : ↥W) : V)
  rw [coe_subFam_apply S₀ a W haW h, coe_subFam_apply S₀ a W haW h', coe_subFam_apply S₀ a W haW h',
    coe_subFam_apply S₀ a W haW h]
  exact LinearMap.congr_fun (hcomm ℓ ℓ' h h') (v : V)

end Sub

end Systems

section Flag

variable (κ : Type*) [CommRing κ]

theorem coeff_aeval_C_mul_X (c : Fin 2 → κ) (F : MvPolynomial (Fin 2) κ) (m : Fin 2 →₀ ℕ) :
    coeff m (aeval (fun j => C (c j) * X j) F) = c 0 ^ (m 0) * c 1 ^ (m 1) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d r =>
    have hmon : aeval (fun j => C (c j) * X j) (monomial d r)
        = monomial d (c 0 ^ (d 0) * c 1 ^ (d 1) * r) := by
      rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
        MvPolynomial.algebraMap_eq, monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp),
        Fin.prod_univ_two, mul_pow, mul_pow, ← C_pow, ← C_pow]
      simp only [map_mul]
      ring
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · ring
  | add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, mul_add]

theorem coeff_binarySubst_of_offdiag (M : Matrix (Fin 2) (Fin 2) ℤ)
    (h01 : ((M 0 1 : ℤ) : κ) = 0) (h10 : ((M 1 0 : ℤ) : κ) = 0)
    (F : MvPolynomial (Fin 2) κ) (m : Fin 2 →₀ ℕ) :
    coeff m (binarySubst κ M F) = ((M 0 0 : ℤ) : κ) ^ (m 0) * ((M 1 1 : ℤ) : κ) ^ (m 1) * coeff m F := by
  set c : Fin 2 → κ := ![((M 0 0 : ℤ) : κ), ((M 1 1 : ℤ) : κ)] with hc
  have hsub : binarySubst κ M = aeval (fun j => C (c j) * X j) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [binarySubst_X, aeval_X, Fin.sum_univ_two]
    fin_cases j
    · simp [hc, h10]
    · simp [hc, h01]
  rw [hsub, coeff_aeval_C_mul_X]
  simp [hc]

theorem coeff_single_one_linear_pow (a b : κ) (k : ℕ) :
    coeff (Finsupp.single 1 k) ((C a * X 0 + C b * X 1) ^ k : MvPolynomial (Fin 2) κ) = b ^ k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', add_mul, coeff_add, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_mul',
      coeff_X_mul']
    have h0 : (0 : Fin 2) ∉ (Finsupp.single (1 : Fin 2) (k + 1)).support := by
      rw [Finsupp.support_single_ne_zero _ (Nat.succ_ne_zero k)]; simp
    have h1 : (1 : Fin 2) ∈ (Finsupp.single (1 : Fin 2) (k + 1)).support := by
      rw [Finsupp.support_single_ne_zero _ (Nat.succ_ne_zero k)]; simp
    rw [if_neg h0, if_pos h1, mul_zero, zero_add,
      show Finsupp.single (1 : Fin 2) (k + 1) - Finsupp.single 1 1 = Finsupp.single 1 k by
        rw [← Finsupp.single_tsub]; rfl,
      ih, pow_succ']

theorem binarySubst_monomial_of_lower (M : Matrix (Fin 2) (Fin 2) ℤ) (h10 : ((M 1 0 : ℤ) : κ) = 0)
    (d : Fin 2 →₀ ℕ) (r : κ) :
    binarySubst κ M (monomial d r) =
      monomial (Finsupp.single 0 (d 0)) (r * ((M 0 0 : ℤ) : κ) ^ (d 0)) *
        (C ((M 0 1 : ℤ) : κ) * X 0 + C ((M 1 1 : ℤ) : κ) * X 1) ^ (d 1) := by
  rw [binarySubst, aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two, h10, C_0, zero_mul, add_zero, MvPolynomial.algebraMap_eq,
    mul_pow, ← C_pow, monomial_eq]
  have hx : ((Finsupp.single (0 : Fin 2) (d 0)).prod fun n e => (X n : MvPolynomial (Fin 2) κ) ^ e)
      = X 0 ^ (d 0) := by
    rw [Finsupp.prod_single_index]
    exact pow_zero _
  rw [hx, C_mul]
  ring

theorem coeff_monomial_single_mul_eq_zero {k : ℕ} (r : κ) (G : MvPolynomial (Fin 2) κ)
    {m : Fin 2 →₀ ℕ} (hm : m 0 < k) : coeff m (monomial (Finsupp.single 0 k) r * G) = 0 := by
  rw [coeff_monomial_mul', if_neg]
  intro h
  have := h 0
  rw [Finsupp.single_eq_same] at this
  omega

variable (n : ℕ)

def W (j : ℕ) : Submodule κ ↥(BinaryForm κ n) where
  carrier := {F | ∀ m : Fin 2 →₀ ℕ, m 0 < j → coeff m (F : MvPolynomial (Fin 2) κ) = 0}
  zero_mem' := fun m _ => by simp
  add_mem' := by
    intro F G hF hG m hm
    simp [hF m hm, hG m hm]
  smul_mem' := by
    intro c F hF m hm
    simp [hF m hm]

theorem mem_W {j : ℕ} (F : ↥(BinaryForm κ n)) :
    F ∈ W κ n j ↔ ∀ m : Fin 2 →₀ ℕ, m 0 < j → coeff m (F : MvPolynomial (Fin 2) κ) = 0 :=
  Iff.rfl

theorem W_zero : W κ n 0 = ⊤ :=
  eq_top_iff.mpr fun _ _ _ hm => absurd hm (Nat.not_lt_zero _)

theorem W_mono {j j' : ℕ} (h : j ≤ j') : W κ n j' ≤ W κ n j :=
  fun _ hF m hm => hF m (lt_of_lt_of_le hm h)

theorem degree_eq_of_coeff_ne_zero {F : MvPolynomial (Fin 2) κ} (hF : F ∈ BinaryForm κ n) {m : Fin 2 →₀ ℕ}
    (hm : coeff m F ≠ 0) : m 0 + m 1 = n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hF
  have h : m.degree = n := by
    by_contra h
    exact hm (hF.coeff_eq_zero h)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
  exact h

theorem W_succ_eq_bot : W κ n (n + 1) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun F hF => Subtype.ext ?_
  refine (MvPolynomial.eq_zero_iff).mpr fun m => ?_
  by_contra h
  have hdeg := degree_eq_of_coeff_ne_zero κ n F.2 h
  exact h (hF m (by omega))

theorem binarySubst_mem_W (M : Matrix (Fin 2) (Fin 2) ℤ) (h10 : ((M 1 0 : ℤ) : κ) = 0) {j : ℕ}
    (F : ↥(BinaryForm κ n)) (hF : F ∈ W κ n j) (m : Fin 2 →₀ ℕ) (hm : m 0 < j) :
    coeff m (binarySubst κ M F) = 0 := by
  classical
  conv_lhs => rw [(F : MvPolynomial (Fin 2) κ).as_sum, map_sum]
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hd0 : j ≤ d 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hF d (by omega))
  rw [binarySubst_monomial_of_lower κ M h10]
  exact coeff_monomial_single_mul_eq_zero κ _ _ (lt_of_lt_of_le hm hd0)

noncomputable def expo (j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 (n - j)

@[scoped simp] theorem expo_zero (j : ℕ) : expo n j 0 = j := by simp [expo]
@[scoped simp] theorem expo_one (j : ℕ) : expo n j 1 = n - j := by simp [expo]

noncomputable def gr (j : ℕ) : ↥(W κ n j) →ₗ[κ] κ where
  toFun F := coeff (expo n j) ((F : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ)
  map_add' F G := by simp
  map_smul' c F := by simp

theorem gr_apply {j : ℕ} (F : ↥(W κ n j)) :
    gr κ n j F = coeff (expo n j) ((F : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ) := rfl

theorem mem_ker_gr_iff {j : ℕ} (F : ↥(W κ n j)) :
    gr κ n j F = 0 ↔ (F : ↥(BinaryForm κ n)) ∈ W κ n (j + 1) := by
  constructor
  · intro h m hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm' | hm'
    · exact F.2 m hm'
    · by_contra hne
      have hdeg := degree_eq_of_coeff_ne_zero κ n (F : ↥(BinaryForm κ n)).2 hne
      have hmeq : m = expo n j := by
        ext i
        fin_cases i
        · simp [hm']
        · simp; omega
      rw [hmeq] at hne
      exact hne h
  · intro h
    exact h (expo n j) (by simp)

variable {κ n} in

theorem exists_gr_eq_one [Nontrivial κ] {j : ℕ} (hj : j ≤ n) : ∃ F : ↥(W κ n j), gr κ n j F = 1 := by
  classical
  have hmem : (monomial (expo n j) (1 : κ)) ∈ BinaryForm κ n := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, expo_zero, expo_one]
    omega
  have hW : (⟨_, hmem⟩ : ↥(BinaryForm κ n)) ∈ W κ n j := by
    intro m hm
    show coeff m (monomial (expo n j) (1 : κ)) = 0
    rw [coeff_monomial, if_neg]
    intro h
    rw [← h, expo_zero] at hm
    exact lt_irrefl _ hm
  refine ⟨⟨_, hW⟩, ?_⟩
  show coeff (expo n j) (monomial (expo n j) (1 : κ)) = 1
  simp

theorem gr_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (h10 : ((M 1 0 : ℤ) : κ) = 0) {j : ℕ}
    (F : ↥(BinaryForm κ n)) (hF : F ∈ W κ n j) :
    coeff (expo n j) (binarySubst κ M F) =
      ((M 0 0 : ℤ) : κ) ^ j * ((M 1 1 : ℤ) : κ) ^ (n - j) * coeff (expo n j) (F : MvPolynomial (Fin 2) κ) := by
  classical
  conv_lhs => rw [(F : MvPolynomial (Fin 2) κ).as_sum, map_sum]
  rw [coeff_sum]

  have hterm : ∀ d ∈ (F : MvPolynomial (Fin 2) κ).support, d ≠ expo n j →
      coeff (expo n j) (binarySubst κ M (monomial d (coeff d (F : MvPolynomial (Fin 2) κ)))) = 0 := by
    intro d hd hne
    have hd0 : j ≤ d 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hd) (hF d (by omega))
    have hdeg := degree_eq_of_coeff_ne_zero κ n F.2 (MvPolynomial.mem_support_iff.mp hd)
    have hlt : j < d 0 := by
      refine lt_of_le_of_ne hd0 fun h => hne ?_
      ext i
      fin_cases i
      · simp [h]
      · simp; omega
    rw [binarySubst_monomial_of_lower κ M h10]
    exact coeff_monomial_single_mul_eq_zero κ _ _ (by simpa using hlt)
  rw [Finset.sum_eq_single (expo n j) (fun d hd hne => hterm d hd hne)
    (fun h => by rw [MvPolynomial.notMem_support_iff.mp h, map_zero, map_zero, coeff_zero])]
  rw [binarySubst_monomial_of_lower κ M h10, coeff_monomial_mul', if_pos (by
      intro i; fin_cases i <;> simp [expo]),
    show expo n j - Finsupp.single 0 (expo n j 0) = Finsupp.single 1 (n - j) by
      ext i; fin_cases i <;> simp [expo],
    expo_zero, expo_one, coeff_single_one_linear_pow]
  ring

end Flag

section Level

variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (N : ℕ) [NeZero N] (hpN : p ∣ N)
  (S₀ : Set ℕ) (n : ℕ)

noncomputable abbrev ρSym : Representation κ (Gamma0 N) ↥(BinaryForm κ n) :=
  (binaryFormRepSL κ n).comp (Gamma0 N).subtype

omit [Fact p.Prime] [CharP κ p] [NeZero N] in
theorem ρSym_apply_coe (γ : Gamma0 N) (F : ↥(BinaryForm κ n)) :
    ((ρSym κ N n γ F : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ) =
      binarySubst κ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) F := rfl

include hpN in
omit [Fact p.Prime] [NeZero N] in

theorem cast_entry_one_zero (γ : Gamma0 N) : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : κ) = 0 := by
  have h := Gamma0_mem.mp γ.2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := (Int.natCast_dvd_natCast.mpr hpN).trans h
  rw [hk, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

omit [Fact p.Prime] [NeZero N] in

theorem Good.ne_p {ℓ : ℕ} (h : Good N S₀ ℓ) (hpN : p ∣ N) : ℓ ≠ p := fun he => h.2.1 (he ▸ hpN)

omit [NeZero N] in
theorem Good.isUnit_pow {ℓ : ℕ} (h : Good N S₀ ℓ) (hpN : p ∣ N) (j : ℕ) : IsUnit ((ℓ : κ) ^ j) := by
  refine (IsUnit.pow j) (isUnit_iff_ne_zero.mpr fun h0 => ?_)
  rw [CharP.cast_eq_zero_iff κ p] at h0
  exact Good.ne_p p N S₀ h hpN ((Nat.prime_dvd_prime_iff_eq Fact.out h.1).mp h0).symm

include hpN in
omit [NeZero N] in
theorem stab_gamma (j : ℕ) (g : Gamma0 N) (v : ↥(BinaryForm κ n)) (hv : v ∈ W κ n j) :
    ρSym κ N n g v ∈ W κ n j := fun m hm =>
  binarySubst_mem_W κ n _ (cast_entry_one_zero p κ N hpN g) v hv m hm

omit [Fact p.Prime] [CharP κ p] [NeZero N] in
theorem stab_alpha (j : ℕ) (ℓ : ℕ) (v : ↥(BinaryForm κ n)) (hv : v ∈ W κ n j) :
    binaryFormAlphaAdj κ n ℓ v ∈ W κ n j := fun m hm =>
  binarySubst_mem_W κ n _ (by simp) v hv m hm

noncomputable def ρW (j : ℕ) : Representation κ (Gamma0 N) ↥(W κ n j) :=
  subRep (ρSym κ N n) (W κ n j) (fun g v hv => stab_gamma p κ N hpN n j g v hv)

noncomputable def aW (j : ℕ) : ℕ → (↥(W κ n j) →ₗ[κ] ↥(W κ n j)) :=
  subFam (N := N) S₀ (fun ℓ => binaryFormAlphaAdj κ n ℓ) (W κ n j) (fun ℓ _ v hv => stab_alpha κ n j ℓ v hv)

omit [Fact p.Prime] [CharP κ p] [NeZero N] in
theorem isCompat_sym (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρSym κ N n) (binaryFormAlphaAdj κ n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj κ n N ℓ u

omit [Fact p.Prime] [CharP κ p] [NeZero N] in
theorem goodCompat_sym : GoodCompat S₀ (ρSym κ N n) (fun ℓ => binaryFormAlphaAdj κ n ℓ) := by
  intro ℓ h u
  haveI := h.neZero
  exact isCompat_sym κ N n ℓ u

def dMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), 0; 0, 1]

theorem dMat_comm (ℓ ℓ' : ℕ) : dMat ℓ * dMat ℓ' = dMat ℓ' * dMat ℓ := by
  simp only [dMat, Matrix.mul_fin_two]
  congr 1 <;> ring

omit [Fact p.Prime] [CharP κ p] in
theorem binaryFormAlphaAdj_eq (ℓ : ℕ) : binaryFormAlphaAdj κ n ℓ = binaryFormRep κ n (dMat ℓ) := rfl

omit [Fact p.Prime] [CharP κ p] in

theorem alpha_comm (ℓ ℓ' : ℕ) :
    binaryFormAlphaAdj κ n ℓ ∘ₗ binaryFormAlphaAdj κ n ℓ' = binaryFormAlphaAdj κ n ℓ' ∘ₗ binaryFormAlphaAdj κ n ℓ := by
  rw [binaryFormAlphaAdj_eq, binaryFormAlphaAdj_eq]
  change binaryFormRep κ n (dMat ℓ) * binaryFormRep κ n (dMat ℓ') =
    binaryFormRep κ n (dMat ℓ') * binaryFormRep κ n (dMat ℓ)
  rw [← map_mul, ← map_mul, dMat_comm]

theorem goodCompat_W (j : ℕ) : GoodCompat (V := ↥(W κ n j)) S₀ (ρW p κ N hpN n j) (aW κ N S₀ n j) :=
  goodCompat_sub S₀ _ _ (W κ n j) _ _ (goodCompat_sym κ N S₀ n)

theorem goodCommute_W (j : ℕ) : GoodCommute S₀ (goodCompat_W p κ N hpN S₀ n j) :=
  goodCommute_of_comm S₀ _ (sub_comm S₀ _ (W κ n j) _ (fun ℓ ℓ' _ _ => alpha_comm κ n ℓ ℓ'))

scoped instance finiteDimensional_binaryForm : FiniteDimensional κ ↥(BinaryForm κ n) := by
  have hle : BinaryForm κ n ≤ MvPolynomial.restrictTotalDegree (Fin 2) κ n := fun φ hφ =>
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.mem_homogeneousSubmodule n φ).mp hφ).totalDegree_le
  exact Submodule.finiteDimensional_of_le hle

abbrev H1W (j : ℕ) : Type := coeffH1 (V := ↥(W κ n j)) (ρW p κ N hpN n j)

scoped instance finiteDimensional_H1W (j : ℕ) : FiniteDimensional κ (H1W p κ N hpN n j) :=
  finiteDimensional_coeffH1 (V := ↥(W κ n j)) N _

def expOf (j : ℕ) : ℕ := n + (p - 3) * j

theorem expOf_modEq (j : ℕ) : expOf p n j + 2 * j ≡ n [MOD (p - 1)] := by
  have hp := (Fact.out : p.Prime).two_le
  rcases Nat.lt_or_ge p 3 with h3 | h3
  · have : p = 2 := by omega
    subst this
    simp [Nat.ModEq, Nat.mod_one]
  · rw [expOf, show n + (p - 3) * j + 2 * j = n + (p - 1) * j by
      rw [show p - 1 = (p - 3) + 2 by omega]; ring]
    exact (Nat.ModEq.symm (Nat.modEq_iff_dvd' (Nat.le_add_right n _) |>.mpr (by simp)))

omit [NeZero N] in

theorem weight_eq_gamma0NebenChar (j : ℕ) (hj : j ≤ n) (γ : Gamma0 N) :
    ((((γ : SL(2, ℤ)) 0 0 : ℤ)) : κ) ^ j * ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : κ) ^ (n - j)
      = gamma0NebenChar p N hpN κ (expOf p n j) γ := by
  set a : κ := (((γ : SL(2, ℤ)) 0 0 : ℤ) : κ) with ha
  set d : κ := (((γ : SL(2, ℤ)) 1 1 : ℤ) : κ) with hd
  have hcast : gamma0NebenChar p N hpN κ (expOf p n j) γ = d ^ expOf p n j := by
    rw [gamma0NebenChar_apply, map_intCast, map_intCast]
  rw [hcast]

  have hdet := Matrix.det_fin_two ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [(γ : SL(2, ℤ)).2] at hdet
  have had : a * d = 1 := by
    have h := congrArg (fun x : ℤ => (x : κ)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, cast_entry_one_zero p κ N hpN γ, mul_zero,
      sub_zero] at h
    rw [ha, hd]; exact h.symm

  have hdp : d ^ (p - 1) = 1 := by
    have hd' : d = ZMod.castHom (dvd_refl p) κ ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod p) := by
      rw [map_intCast]
    have hne : ((((γ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod p) ≠ 0 := by
      intro h0
      rw [hd', h0, map_zero, mul_zero] at had
      exact zero_ne_one had
    rw [hd', ← map_pow, ZMod.pow_card_sub_one_eq_one hne, map_one]
  have hp2 := (Fact.out : p.Prime).two_le
  rcases Nat.lt_or_ge p 3 with h3 | h3
  ·
    have hp2' : p = 2 := by omega
    have hd1 : d = 1 := by rw [hp2'] at hdp; simpa using hdp
    have ha1 : a = 1 := by rw [hd1, mul_one] at had; exact had
    rw [ha1, hd1, one_pow, one_pow, one_pow, mul_one]
  ·
    have hainv : d ^ (p - 2) = a := by
      have h1 : d ^ (p - 2) * d = a * d := by
        rw [← pow_succ, show p - 2 + 1 = p - 1 by omega, hdp, had]
      have hd0 : d ≠ 0 := fun h0 => by rw [h0, mul_zero] at had; exact zero_ne_one had
      exact mul_right_cancel₀ hd0 h1
    rw [expOf, show n + (p - 3) * j = (n - j) + (p - 2) * j by
        rw [show p - 2 = (p - 3) + 1 by omega]; ring_nf; omega,
      pow_add, pow_mul, hainv, mul_comm]

omit [Fact p.Prime] [NeZero N] in

theorem goodCompat_neben (e j : ℕ) :
    GoodCompat S₀ (gamma0NebenRep p N hpN κ e) (fun ℓ => ((ℓ : κ) ^ j) • (LinearMap.id : κ →ₗ[κ] κ)) := by
  intro ℓ h u
  haveI := h.neZero
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, gamma0NebenRep_apply,
    smul_eq_mul]
  have hdd : gamma0NebenChar p N hpN κ e (heckeConj N ℓ u) = gamma0NebenChar p N hpN κ e (u : Gamma0 N) := by
    rw [gamma0NebenChar_apply, gamma0NebenChar_apply]
    rfl
  rw [hdd]
  ring

omit [Fact p.Prime] [NeZero N] in
theorem goodCompat_neben_id (e : ℕ) :
    GoodCompat S₀ (gamma0NebenRep p N hpN κ e) (fun _ => (LinearMap.id : κ →ₗ[κ] κ)) := by
  intro ℓ h u
  haveI := h.neZero
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply, gamma0NebenRep_apply]
  have hdd : gamma0NebenChar p N hpN κ e (heckeConj N ℓ u) = gamma0NebenChar p N hpN κ e (u : Gamma0 N) := by
    rw [gamma0NebenChar_apply, gamma0NebenChar_apply]
    rfl
  rw [hdd]

def Goal (lam : ℕ → κ) : Prop :=
  ∃ (j e : ℕ) (nu : ℕ → κ), j ≤ n ∧ e + 2 * j ≡ n [MOD (p - 1)] ∧
    IsEigensystemH1 N (gamma0NebenRep p N hpN κ e) (fun _ => LinearMap.id) S₀ nu ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) ^ j * nu ℓ

theorem goal_of_piece (lam : ℕ → κ) (j : ℕ) (hj : j ≤ n) (y : coeffH1 (gamma0NebenRep p N hpN κ (expOf p n j)))
    (hy : y ≠ 0) (heig : IsEigvec S₀ (goodCompat_neben p κ N hpN S₀ (expOf p n j) j) lam y) :
    Goal p κ N hpN S₀ n lam := by
  classical
  let nu : ℕ → κ := fun ℓ => ((ℓ : κ) ^ j)⁻¹ * lam ℓ
  refine ⟨j, expOf p n j, nu, hj, expOf_modEq p n j, ?_, ?_⟩
  · have h1 : IsEigensystemH1 N (gamma0NebenRep p N hpN κ (expOf p n j))
        (fun ℓ => ((ℓ : κ) ^ j) • (LinearMap.id : κ →ₗ[κ] κ)) S₀ lam :=
      (isEigensystemH1_iff S₀ (goodCompat_neben p κ N hpN S₀ (expOf p n j) j) lam).mpr ⟨y, hy, heig⟩
    exact isEigensystemH1_of_smul_of_mul_eq_one N _ (fun _ => LinearMap.id)
      (fun ℓ => ((ℓ : κ) ^ j) • (LinearMap.id : κ →ₗ[κ] κ)) (fun ℓ => (ℓ : κ) ^ j)
      (fun ℓ => ((ℓ : κ) ^ j)⁻¹) S₀ lam (fun ℓ _ _ _ => rfl)
      (fun ℓ hℓ hℓN hℓS => inv_mul_cancel₀ (Good.isUnit_pow p κ N S₀ ⟨hℓ, hℓN, hℓS⟩ hpN j).ne_zero) h1
  · intro ℓ hℓ hℓN hℓS
    show lam ℓ = (ℓ : κ) ^ j * (((ℓ : κ) ^ j)⁻¹ * lam ℓ)
    rw [← mul_assoc, mul_inv_cancel₀ (Good.isUnit_pow p κ N S₀ ⟨hℓ, hℓN, hℓS⟩ hpN j).ne_zero, one_mul]

theorem descend (lam : ℕ → κ) : ∀ (d k : ℕ), k + d = n + 1 →
    (∃ x : H1W p κ N hpN n k, x ≠ 0 ∧ IsEigvec S₀ (goodCompat_W p κ N hpN S₀ n k) lam x) →
      Goal p κ N hpN S₀ n lam := by
  intro d
  induction d with
  | zero =>
    rintro k hk ⟨x, hx, -⟩
    exfalso
    apply hx
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
    have hz : z = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      have hmem : (((z : Gamma0 N → ↥(W κ n k)) g : ↥(W κ n k)) : ↥(BinaryForm κ n)) ∈ W κ n (n + 1) := by
        rw [← show k = n + 1 by omega]
        exact ((z : Gamma0 N → ↥(W κ n k)) g).2
      rw [W_succ_eq_bot, Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    rw [hz, map_zero]
  | succ d ih =>
    rintro k hk ⟨x, hx, heig⟩
    have hkn : k ≤ n := by omega

    have hle : W κ n (k + 1) ≤ W κ n k := W_mono κ n (Nat.le_succ k)
    let incl : ↥(W κ n (k + 1)) →ₗ[κ] ↥(W κ n k) := Submodule.inclusion hle
    let πk : ↥(W κ n k) →ₗ[κ] κ := gr κ n k
    have hincl : ∀ g : Gamma0 N,
        incl ∘ₗ ρW p κ N hpN n (k + 1) g = ρW p κ N hpN n k g ∘ₗ incl :=
      fun g => LinearMap.ext fun v => Subtype.ext rfl
    have hincla : ∀ ℓ, Good N S₀ ℓ →
        incl ∘ₗ aW κ N S₀ n (k + 1) ℓ = aW κ N S₀ n k ℓ ∘ₗ incl := by
      intro ℓ h
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (((aW κ N S₀ n (k + 1) ℓ v) : ↥(W κ n (k + 1))) : ↥(BinaryForm κ n)) =
        ((aW κ N S₀ n k ℓ (incl v) : ↥(W κ n k)) : ↥(BinaryForm κ n))
      rw [aW, aW, coe_subFam_apply S₀ _ _ _ h, coe_subFam_apply S₀ _ _ _ h]
      rfl
    have hπρ : ∀ g : Gamma0 N, πk ∘ₗ ρW p κ N hpN n k g = gamma0NebenRep p N hpN κ (expOf p n k) g ∘ₗ πk := by
      intro g
      refine LinearMap.ext fun v => ?_
      change coeff (expo n k) (binarySubst κ ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (v : ↥(BinaryForm κ n)))
        = gamma0NebenChar p N hpN κ (expOf p n k) g * coeff (expo n k) ((v : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ)
      rw [gr_binarySubst κ n _ (cast_entry_one_zero p κ N hpN g) _ v.2, weight_eq_gamma0NebenChar p κ N hpN n k hkn g]
    have hπa : ∀ ℓ, Good N S₀ ℓ →
        πk ∘ₗ aW κ N S₀ n k ℓ = (((ℓ : κ) ^ k) • (LinearMap.id : κ →ₗ[κ] κ)) ∘ₗ πk := by
      intro ℓ h
      refine LinearMap.ext fun v => ?_
      change coeff (expo n k) ((((aW κ N S₀ n k ℓ v) : ↥(W κ n k)) : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ) =
        ((ℓ : κ) ^ k) • coeff (expo n k) ((v : ↥(BinaryForm κ n)) : MvPolynomial (Fin 2) κ)
      rw [aW, coe_subFam_apply S₀ _ _ _ h, binaryFormAlphaAdj_apply_coe,
        coeff_binarySubst_of_offdiag κ _ (by simp) (by simp)]
      simp
    have hinj : Function.Injective incl := Submodule.inclusion_injective hle
    have hexact : LinearMap.range incl = LinearMap.ker πk := by
      apply le_antisymm
      · rintro _ ⟨v, rfl⟩
        rw [LinearMap.mem_ker]
        exact (mem_ker_gr_iff κ n (incl v)).mpr v.2
      · intro v hv
        rw [LinearMap.mem_ker] at hv
        exact ⟨⟨(v : ↥(BinaryForm κ n)), (mem_ker_gr_iff κ n v).mp hv⟩, rfl⟩
    have hπsurj : Function.Surjective πk := by
      intro c
      obtain ⟨F, hF⟩ := exists_gr_eq_one (κ := κ) (n := n) hkn
      exact ⟨c • F, by rw [map_smul, smul_eq_mul]; change c * gr κ n k F = c; rw [hF, mul_one]⟩
    haveI : FiniteDimensional κ (coeffH1 (V := ↥(W κ n (k + 1))) (ρW p κ N hpN n (k + 1))) :=
      finiteDimensional_H1W p κ N hpN n (k + 1)
    have hres := step (V' := ↥(W κ n (k + 1))) (V := ↥(W κ n k)) (V'' := κ) S₀
      (goodCompat_W p κ N hpN S₀ n (k + 1)) (goodCompat_W p κ N hpN S₀ n k)
      (goodCompat_neben p κ N hpN S₀ (expOf p n k) k) incl hincl hincla πk hπρ hπa
      (goodCommute_W p κ N hpN S₀ n (k + 1)) hinj hexact hπsurj lam x hx heig
    rcases hres with ⟨y, hy, hyeig⟩ | ⟨y, hy, hyeig⟩
    · exact goal_of_piece p κ N hpN S₀ n lam k hkn y hy hyeig
    · exact ih (k + 1) (by omega) ⟨y, hy, hyeig⟩

theorem top (lam : ℕ → κ) (x : coeffH1 (ρSym κ N n)) (hx : x ≠ 0)
    (heig : IsEigvec S₀ (goodCompat_sym κ N S₀ n) lam x) :
    ∃ y : H1W p κ N hpN n 0, y ≠ 0 ∧ IsEigvec S₀ (goodCompat_W p κ N hpN S₀ n 0) lam y := by
  have hW0 : W κ n 0 = ⊤ := W_zero κ n
  let e : ↥(BinaryForm κ n) →ₗ[κ] ↥(W κ n 0) :=
    LinearMap.codRestrict (W κ n 0) LinearMap.id (fun v => by rw [hW0]; trivial)
  have he : ∀ g : Gamma0 N, e ∘ₗ ρSym κ N n g = ρW p κ N hpN n 0 g ∘ₗ e :=
    fun g => LinearMap.ext fun v => Subtype.ext rfl
  have hea : ∀ ℓ, Good N S₀ ℓ → e ∘ₗ binaryFormAlphaAdj κ n ℓ = aW κ N S₀ n 0 ℓ ∘ₗ e := by
    intro ℓ h
    refine LinearMap.ext fun v => Subtype.ext ?_
    change binaryFormAlphaAdj κ n ℓ v = ((aW κ N S₀ n 0 ℓ (e v) : ↥(W κ n 0)) : ↥(BinaryForm κ n))
    rw [aW, coe_subFam_apply S₀ _ _ _ h]
    rfl
  have hsub : ∀ g : Gamma0 N,
      (W κ n 0).subtype ∘ₗ ρW p κ N hpN n 0 g = ρSym κ N n g ∘ₗ (W κ n 0).subtype :=
    fun g => LinearMap.ext fun v => rfl
  refine ⟨H1map (V := ↥(BinaryForm κ n)) (W := ↥(W κ n 0)) N (ρSym κ N n) (ρW p κ N hpN n 0) e he x, ?_,
    isEigvec_H1map (V := ↥(BinaryForm κ n)) (W := ↥(W κ n 0)) S₀ (goodCompat_sym κ N S₀ n)
      (goodCompat_W p κ N hpN S₀ n 0) e he hea heig⟩
  intro h0
  apply hx
  have hret : H1map (V := ↥(W κ n 0)) (W := ↥(BinaryForm κ n)) N (ρW p κ N hpN n 0) (ρSym κ N n)
      (W κ n 0).subtype hsub
      (H1map (V := ↥(BinaryForm κ n)) (W := ↥(W κ n 0)) N (ρSym κ N n) (ρW p κ N hpN n 0) e he x) = x := by
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
    rw [H1map_mk, H1map_mk]
    congr 1
  rw [← hret, h0, map_zero]

end Level

end ASF
p2m_reactivate "P2MW.S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd.ASF"

open scoped MatrixGroups in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : p ∣ N) (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ (j e : ℕ) (nu : ℕ → κ), j ≤ n ∧ e + 2 * j ≡ n [MOD (p - 1)] ∧
      HeckeEis.IsEigensystemH1 N (HeckeEis.gamma0NebenRep p N hpN κ e)
        (fun _ => LinearMap.id) S₀ nu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) ^ j * nu ℓ := by
  open ASF in
  obtain ⟨x, hx, heig⟩ := (isEigensystemH1_iff S₀ (goodCompat_sym κ N S₀ n) lam).mp hocc
  obtain ⟨y, hy, hyeig⟩ := top p κ N hpN S₀ n lam x hx heig
  exact descend p κ N hpN S₀ n lam (n + 1) 0 (by omega) ⟨y, hy, hyeig⟩

end S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd
end P2MW
export P2MW.S_HeckeEis_exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd (solution)
