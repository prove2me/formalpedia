-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_or_of_isEigensystemH1_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/34a0cec9-6c3b-5ada-bf03-11cf604b4e89

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_ModularCurve_index_heckeUpper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective

set_option autoImplicit false

namespace PushH1

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

section Inj

variable {K : Type*} [CommRing K]
variable {V' V : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ' : Representation K (Gamma0 N) V') (ρ : Representation K (Gamma0 N) V)
variable (ι : V' →ₗ[K] V) (hι : ∀ g : Gamma0 N, ι ∘ₗ ρ' g = ρ g ∘ₗ ι) (hinj : Function.Injective ι)

include hι hinj in

theorem isCompat_of_injective (ℓ : ℕ) [NeZero ℓ] (a' : V' →ₗ[K] V') (a : V →ₗ[K] V)
    (hιa : ι ∘ₗ a' = a ∘ₗ ι) (ha : IsCompat N ℓ ρ a) : IsCompat N ℓ ρ' a' := by
  intro u
  refine LinearMap.ext fun v => hinj ?_
  change ι (a' (ρ' _ v)) = ι (ρ' _ (a' v))
  have h1 : ι (a' (ρ' (heckeConj N ℓ u) v)) = a (ρ (heckeConj N ℓ u) (ι v)) := by
    rw [show ι (a' _) = a (ι _) from LinearMap.congr_fun hιa _, f_ρ N ρ' ρ ι hι]
  have h2 : ι (ρ' (u : Gamma0 N) (a' v)) = ρ (u : Gamma0 N) (a (ι v)) := by
    rw [f_ρ N ρ' ρ ι hι, show ι (a' _) = a (ι _) from LinearMap.congr_fun hιa _]
  rw [h1, h2]
  exact LinearMap.congr_fun (ha u) (ι v)

theorem coeffHeckeFun_coboundary (ℓ : ℕ) [NeZero ℓ] (a : V →ₗ[K] V) (ha : IsCompat N ℓ ρ a) (v : V) :
    coeffHeckeFun N ℓ ρ a (coeffCoboundaryMap ρ v) =
      coeffCoboundaryMap ρ
        (letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
         ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, ρ q.out (a v)) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  rw [coeffHeckeFun_apply, coeffCoboundaryMap_apply, map_sum]
  simp only [coeffCoboundaryMap_apply, map_sub]
  have hcomp : ∀ q : Gamma0 N ⧸ heckeUpper N ℓ,
      ρ (g • q).out (a (ρ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q)) v))
        = ρ g (ρ q.out (a v)) := by
    intro q
    have h1 : a (ρ (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q)) v)
        = ρ (transferAux (heckeUpper N ℓ) g q : Gamma0 N) (a v) := LinearMap.congr_fun (ha _) v
    rw [h1]
    change (ρ (g • q).out * ρ (transferAux (heckeUpper N ℓ) g q : Gamma0 N)) (a v)
      = (ρ g * ρ q.out) (a v)
    rw [← map_mul, ← map_mul]
    congr 2
    rw [coe_transferAux, mul_inv_cancel_left]
  simp only [hcomp]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact Fintype.sum_bijective (g • ·) (MulAction.bijective g)
    (fun q : Gamma0 N ⧸ heckeUpper N ℓ => ρ (g • q).out (a v))
    (fun q : Gamma0 N ⧸ heckeUpper N ℓ => ρ q.out (a v)) fun q => rfl

end Inj

section Kernel

variable {K : Type*} [Field K]
variable {V' V : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ' : Representation K (Gamma0 N) V') (ρ : Representation K (Gamma0 N) V)
variable (ι : V' →ₗ[K] V) (hι : ∀ g : Gamma0 N, ι ∘ₗ ρ' g = ρ g ∘ₗ ι) (hinj : Function.Injective ι)
variable (q₀ : V) (hq₀ : ∀ v : V, (∀ g : Gamma0 N, ρ g v - v ∈ LinearMap.range ι) →
  ∃ r : K, v - r • q₀ ∈ LinearMap.range ι)

include hι in
theorem rho_mem_range (g : Gamma0 N) {x : V} (hx : x ∈ LinearMap.range ι) : ρ g x ∈ LinearMap.range ι := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨ρ' g y, f_ρ N ρ' ρ ι hι g y⟩

include hι hinj hq₀ in

theorem exists_of_H1map_eq_zero (z' : ↥(coeffCocycles ρ'))
    (h0 : H1map N ρ' ρ ι hι (coeffH1Mk ρ' z') = 0) (hne : coeffH1Mk ρ' z' ≠ 0) :
    ∃ (vt : V) (r : K), r ≠ 0 ∧ (∀ g, ρ g vt - vt = ι ((z' : Gamma0 N → V') g)) ∧
      vt - r • q₀ ∈ LinearMap.range ι ∧ ∀ g : Gamma0 N, ρ g q₀ - q₀ ∈ LinearMap.range ι := by
  rw [H1map_mk, coeffH1Mk_eq_zero_iff] at h0
  obtain ⟨vt, hvt⟩ := (mem_coeffCoboundaries_iff ρ _).mp h0
  have hvtg : ∀ g, ρ g vt - vt = ι ((z' : Gamma0 N → V') g) := fun g => congrFun hvt g
  obtain ⟨r, hr⟩ := hq₀ vt fun g => ⟨_, (hvtg g).symm⟩
  by_cases hr0 : r = 0
  · exfalso
    apply hne
    rw [hr0, zero_smul, sub_zero] at hr
    obtain ⟨v', hv'⟩ := hr
    rw [coeffH1Mk_eq_zero_iff]
    refine (mem_coeffCoboundaries_iff ρ' _).mpr ⟨v', funext fun g => hinj ?_⟩
    rw [← hvtg g, ← hv', map_sub, f_ρ N ρ' ρ ι hι]
  refine ⟨vt, r, hr0, hvtg, hr, fun g => ?_⟩

  have hmem : ρ g (vt - r • q₀) - (vt - r • q₀) ∈ LinearMap.range ι :=
    Submodule.sub_mem _ (rho_mem_range N ρ' ρ ι hι g hr) hr
  have hz : ρ g vt - vt ∈ LinearMap.range ι := ⟨_, (hvtg g).symm⟩
  have hkey : r • (ρ g q₀ - q₀) = (ρ g vt - vt) - (ρ g (vt - r • q₀) - (vt - r • q₀)) := by
    simp only [map_sub, map_smul, smul_sub]
    abel
  have hmem' : r • (ρ g q₀ - q₀) ∈ LinearMap.range ι := by
    rw [hkey]; exact Submodule.sub_mem _ hz hmem
  have := Submodule.smul_mem _ r⁻¹ hmem'
  rwa [smul_smul, inv_mul_cancel₀ hr0, one_smul] at this

include hι in

theorem rho_congr (hq₀inv : ∀ g : Gamma0 N, ρ g q₀ - q₀ ∈ LinearMap.range ι) (g : Gamma0 N) (s : K)
    {x : V} (hx : x - s • q₀ ∈ LinearMap.range ι) : ρ g x - s • q₀ ∈ LinearMap.range ι := by
  have h1 : ρ g x - s • q₀ = ρ g (x - s • q₀) + s • (ρ g q₀ - q₀) := by
    simp only [map_sub, map_smul, smul_sub]; abel
  rw [h1]
  exact Submodule.add_mem _ (rho_mem_range N ρ' ρ ι hι g hx) (Submodule.smul_mem _ _ (hq₀inv g))

include hι hinj in

theorem heckeZ1_sub_smul_mem (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (a' : V' →ₗ[K] V') (a : V →ₗ[K] V) (hιa : ι ∘ₗ a' = a ∘ₗ ι) (ha : IsCompat N ℓ ρ a)
    (c : K) (hc : a q₀ - c • q₀ ∈ LinearMap.range ι)
    (hq₀inv : ∀ g : Gamma0 N, ρ g q₀ - q₀ ∈ LinearMap.range ι)
    (z' : ↥(coeffCocycles ρ')) (vt : V) (r : K)
    (hvt : ∀ g, ρ g vt - vt = ι ((z' : Gamma0 N → V') g)) (hr : vt - r • q₀ ∈ LinearMap.range ι) :
    (heckeZ1 (isCompat_of_injective N ρ' ρ ι hι hinj ℓ a' a hιa ha) z' : Gamma0 N → V')
        - (((ℓ : K) + 1) * c) • (z' : Gamma0 N → V') ∈ coeffCoboundaries ρ' := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  set w : V := ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, ρ q.out (a vt) with hw

  have hιz : ι ∘ (z' : Gamma0 N → V') = coeffCoboundaryMap ρ vt := funext fun g => (hvt g).symm
  have hT : ι ∘ (heckeZ1 (isCompat_of_injective N ρ' ρ ι hι hinj ℓ a' a hιa ha) z' : Gamma0 N → V')
      = coeffCoboundaryMap ρ w := by
    rw [coe_heckeZ1, comp_coeffHeckeFun N ρ' ρ ι hι a' a hιa ℓ, hιz, coeffHeckeFun_coboundary N ρ ℓ a ha]

  have havt : a vt - (r * c) • q₀ ∈ LinearMap.range ι := by
    obtain ⟨v', hv'⟩ := hr
    have h1 : a vt - (r * c) • q₀ = a (ι v') + r • (a q₀ - c • q₀) := by
      have : vt = ι v' + r • q₀ := by rw [hv']; abel
      rw [this, map_add, map_smul, smul_sub, mul_smul]
      abel
    rw [h1]
    refine Submodule.add_mem _ ⟨a' v', ?_⟩ (Submodule.smul_mem _ _ hc)
    exact LinearMap.congr_fun hιa v'

  have hcard : (Finset.univ : Finset (Gamma0 N ⧸ heckeUpper N ℓ)).card = ℓ + 1 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card,
      ModularCurve.index_heckeUpper hℓ hℓN]
  have hwq : w - (((ℓ : K) + 1) * (r * c)) • q₀ ∈ LinearMap.range ι := by
    have hsum : w - (((ℓ : K) + 1) * (r * c)) • q₀
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, (ρ q.out (a vt) - (r * c) • q₀) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, ← hw, mul_smul, ← Nat.cast_smul_eq_nsmul K,
        Nat.cast_add, Nat.cast_one]
    rw [hsum]
    exact Submodule.sum_mem _ fun q _ => rho_congr N ρ' ρ ι hι q₀ hq₀inv _ _ havt

  obtain ⟨s, hs⟩ := hwq
  obtain ⟨v', hv'⟩ := hr
  have hw' : w = (((ℓ : K) + 1) * c) • vt + ι (s - (((ℓ : K) + 1) * c) • v') := by
    have e1 : w = ι s + (((ℓ : K) + 1) * (r * c)) • q₀ := by rw [hs]; abel
    have e2 : r • q₀ = vt - ι v' := by rw [hv']; abel
    rw [e1, map_sub, map_smul, show (((ℓ : K) + 1) * (r * c)) • q₀ = (((ℓ : K) + 1) * c) • (r • q₀) by
      rw [smul_smul]; ring_nf, e2, smul_sub]
    abel
  set s' := s - (((ℓ : K) + 1) * c) • v' with hs'
  refine (mem_coeffCoboundaries_iff ρ' _).mpr ⟨s', funext fun g => hinj ?_⟩
  have hTg := congrFun hT g
  simp only [Function.comp_apply, coeffCoboundaryMap_apply] at hTg
  have lhs : ι (ρ' g s' - s') = ρ g (ι s') - ι s' := by rw [map_sub, f_ρ N ρ' ρ ι hι]
  have rhs : ι ((heckeZ1 (isCompat_of_injective N ρ' ρ ι hι hinj ℓ a' a hιa ha) z' : Gamma0 N → V') g
        - (((ℓ : K) + 1) * c) • (z' : Gamma0 N → V') g)
      = (ρ g w - w) - (((ℓ : K) + 1) * c) • (ρ g vt - vt) := by
    rw [map_sub, map_smul, hTg, hvt g]
  change ι (ρ' g s' - s') = ι ((heckeZ1 _ z' : Gamma0 N → V') g - (((ℓ : K) + 1) * c) • (z' : Gamma0 N → V') g)
  rw [lhs, rhs, hw', map_add, map_smul]
  simp only [smul_sub]
  abel

end Kernel

section Main

variable {K : Type*} [Field K]
variable {V' V : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]

theorem main (N : ℕ) (S₀ : Set ℕ)
    (ρ' : Representation K (Gamma0 N) V') (ρ : Representation K (Gamma0 N) V)
    (a' : ℕ → (V' →ₗ[K] V')) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(heckeUpper N ℓ), a ℓ ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a ℓ)
    (ι : V' →ₗ[K] V) (hι : ∀ g : Gamma0 N, ι ∘ₗ ρ' g = ρ g ∘ₗ ι)
    (hιa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ι ∘ₗ a' ℓ = a ℓ ∘ₗ ι) (hinj : Function.Injective ι)
    (q₀ : V) (hq₀ : ∀ v : V, (∀ g : Gamma0 N, ρ g v - v ∈ LinearMap.range ι) →
      ∃ r : K, v - r • q₀ ∈ LinearMap.range ι)
    (c : ℕ → K) (hc : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a ℓ q₀ - c ℓ • q₀ ∈ LinearMap.range ι)
    (lam : ℕ → K) (h : IsEigensystemH1 N ρ' a' S₀ lam) :
    IsEigensystemH1 N ρ a S₀ lam ∨
      ((∀ g : Gamma0 N, ρ g q₀ - q₀ ∈ LinearMap.range ι) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = ((ℓ : K) + 1) * c ℓ) := by
  obtain ⟨x, hx, heig⟩ := h
  obtain ⟨z', rfl⟩ := coeffH1Mk_surjective ρ' x

  have hc' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; IsCompat N ℓ ρ' (a' ℓ) := fun ℓ hℓ hℓN hℓS => by
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact isCompat_of_injective N ρ' ρ ι hι hinj ℓ (a' ℓ) (a ℓ) (hιa ℓ hℓ hℓN hℓS) (ha ℓ hℓ hℓN hℓS)
  have heig' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S₀),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      heckeH1 (hc' ℓ hℓ hℓN hℓS) (coeffH1Mk ρ' z') = lam ℓ • coeffH1Mk ρ' z' := by
    intro ℓ hℓ hℓN hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
    have hT' : IsCoeffHeckeOnH1 N ℓ ρ' (a' ℓ) T := hT
    rw [eq_heckeH1_of_isCoeffHeckeOnH1 (hc' ℓ hℓ hℓN hℓS) hT'] at hTx
    exact hTx
  by_cases h0 : H1map N ρ' ρ ι hι (coeffH1Mk ρ' z') = 0
  swap
  ·
    left
    refine ⟨H1map N ρ' ρ ι hι (coeffH1Mk ρ' z'), h0, fun ℓ hℓ hℓN hℓS => ?_⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    refine ⟨heckeH1 (ha ℓ hℓ hℓN hℓS), isCoeffHeckeOnH1_heckeH1 _, ?_⟩
    rw [← H1map_heckeH1 N ρ' ρ ι hι (a' ℓ) (a ℓ) (hιa ℓ hℓ hℓN hℓS) ℓ (hc' ℓ hℓ hℓN hℓS) (ha ℓ hℓ hℓN hℓS),
      heig' ℓ hℓ hℓN hℓS, map_smul]
  · right
    obtain ⟨vt, r, hr0, hvt, hr, hinv⟩ := exists_of_H1map_eq_zero N ρ' ρ ι hι hinj q₀ hq₀ z' h0 hx
    refine ⟨hinv, fun ℓ hℓ hℓN hℓS => ?_⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hcob := heckeZ1_sub_smul_mem N ρ' ρ ι hι hinj q₀ ℓ hℓ hℓN (a' ℓ) (a ℓ) (hιa ℓ hℓ hℓN hℓS)
      (ha ℓ hℓ hℓN hℓS) (c ℓ) (hc ℓ hℓ hℓN hℓS) hinv z' vt r hvt hr

    have hTe : heckeH1 (hc' ℓ hℓ hℓN hℓS) (coeffH1Mk ρ' z') = (((ℓ : K) + 1) * c ℓ) • coeffH1Mk ρ' z' := by
      rw [heckeH1_mk, ← map_smul, coeffH1Mk_eq_iff]
      have hpi : heckeZ1 (hc' ℓ hℓ hℓN hℓS) z'
          = heckeZ1 (isCompat_of_injective N ρ' ρ ι hι hinj ℓ (a' ℓ) (a ℓ) (hιa ℓ hℓ hℓN hℓS)
              (ha ℓ hℓ hℓN hℓS)) z' := rfl
      rw [hpi]
      exact hcob
    have h2 := (heig' ℓ hℓ hℓN hℓS).symm.trans hTe
    have h3 : (lam ℓ - (((ℓ : K) + 1) * c ℓ)) • coeffH1Mk ρ' z' = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hx

end Main

end PushH1
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective.PushH1"

open scoped MatrixGroups in
theorem solution
    (N : ℕ) {K : Type} [Field K] (S₀ : Set ℕ)
    {V' V : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]
    (ρ' : Representation K (CongruenceSubgroup.Gamma0 N) V') (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a' : ℕ → (V' →ₗ[K] V')) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (ι : V' →ₗ[K] V) (hι : ∀ g : CongruenceSubgroup.Gamma0 N, ι ∘ₗ ρ' g = ρ g ∘ₗ ι)
    (hιa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ι ∘ₗ a' ℓ = a ℓ ∘ₗ ι) (hinj : Function.Injective ι)
    (q₀ : V) (hq₀ : ∀ v : V, (∀ g : CongruenceSubgroup.Gamma0 N, ρ g v - v ∈ LinearMap.range ι) →
      ∃ r : K, v - r • q₀ ∈ LinearMap.range ι)
    (c : ℕ → K) (hc : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a ℓ q₀ - c ℓ • q₀ ∈ LinearMap.range ι)
    (lam : ℕ → K) (h : HeckeEis.IsEigensystemH1 N ρ' a' S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam ∨
      ((∀ g : CongruenceSubgroup.Gamma0 N, ρ g q₀ - q₀ ∈ LinearMap.range ι) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = ((ℓ : K) + 1) * c ℓ) :=
  PushH1.main N S₀ ρ' ρ a' a ha ι hι hιa hinj q₀ hq₀ c hc lam h

end S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective (solution)
