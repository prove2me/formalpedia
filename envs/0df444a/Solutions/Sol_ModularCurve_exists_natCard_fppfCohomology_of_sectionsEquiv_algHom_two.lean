-- Prove2me | solution 1 for ModularCurve.exists_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/98db5565-a7ff-54a7-b539-e963d96e16f1

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.TensorProduct.Basic
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction
import Theorems.Thm_AlgebraicGeometry_fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial
import Theorems.Thm_AlgebraicGeometry_natCard_fppfH1_Gm_specZ_eq_one
import Theorems.Thm_AlgebraicGeometry_subsingleton_fppfH1_constantZMod_specZ_of_prime
import Theorems.Thm_ModularCurve_iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
p2m_attr_erase "simp" "Algebra.DescentCofaces.i₁_apply Algebra.DescentCofaces.i₂_apply Algebra.DescentCofaces.c₁₂_tmul Algebra.DescentCofaces.c₂₃_tmul Algebra.DescentCofaces.c₁₃_tmul"

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

noncomputable section

namespace ETABLEDM

theorem mem_ratLocalizedAt_iff {l : ℕ} {q : ℚ} :
    q ∈ GaloisRep.ratLocalizedAt l ↔ q.den.Coprime l := Iff.rfl

def ratVS (l : ℕ) (hl : l.Prime) : ValuationSubring ℚ :=
  { GaloisRep.ratLocalizedAt l with
    mem_or_inv_mem' := fun x => by
      rcases eq_or_ne x 0 with rfl | hx
      · exact Or.inl (mem_ratLocalizedAt_iff.mpr (by simp))
      · rcases Nat.coprime_or_dvd_of_prime hl x.den with h | h
        · exact Or.inl (mem_ratLocalizedAt_iff.mpr h.symm)
        · refine Or.inr (mem_ratLocalizedAt_iff.mpr ?_)
          rw [Rat.den_inv_of_ne_zero hx]
          have hnd : ¬ l ∣ x.num.natAbs := by
            intro hdvd
            have h1 : l ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd hdvd h
            rw [x.reduced] at h1
            exact hl.ne_one (Nat.dvd_one.mp h1)
          exact ((Nat.Prime.coprime_iff_not_dvd hl).mpr hnd).symm }

theorem ratLocalized_integers (l : ℕ) (hl : l.Prime) :
    (ratVS l hl).valuation.Integers ↥(GaloisRep.ratLocalizedAt l) where
  hom_inj := Subtype.coe_injective
  map_le_one x := ((ratVS l hl).valuation_le_one_iff _).mpr x.2
  exists_of_le_one {r} hr := ⟨⟨r, ((ratVS l hl).valuation_le_one_iff _).mp hr⟩, rfl⟩

theorem ratVS_integers (l : ℕ) (hl : l.Prime) :
    (ratVS l hl).valuation.Integers ↥(ratVS l hl) where
  hom_inj := Subtype.coe_injective
  map_le_one x := ((ratVS l hl).valuation_le_one_iff _).mpr x.2
  exists_of_le_one {r} hr := ⟨⟨r, ((ratVS l hl).valuation_le_one_iff _).mp hr⟩, rfl⟩

theorem den_coprime_of_isIntegral (l : ℕ) (hl : l.Prime) {x : ℚ}
    (hx : _root_.IsIntegral ↥(GaloisRep.ratLocalizedAt l) x) : x.den.Coprime l := by
  have h1 : x ∈ (ratVS l hl).valuation.integer :=
    Valuation.Integers.mem_of_integral (ratLocalized_integers l hl) hx
  have h2 : (ratVS l hl).valuation x ≤ 1 := h1
  exact mem_ratLocalizedAt_iff.mp (((ratVS l hl).valuation_le_one_iff x).mp h2)

theorem den_coprime_of_finite (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (l : ℕ) (hl : l.Prime)
    (hfin : Module.Finite (GaloisRep.ratLocalizedAt l)
      (TensorProduct ℤ (GaloisRep.ratLocalizedAt l) K))
    (ψ : K →ₐ[ℤ] ℚ) (k : K) : (ψ k).den.Coprime l := by
  refine den_coprime_of_isIntegral l hl ?_
  refine IsIntegral.of_mem_of_fg
    (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt l) (Set.range ⇑ψ)) ?_ _
    (Algebra.subset_adjoin ⟨k, rfl⟩)
  let L : TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt l) K
      →ₗ[↥(GaloisRep.ratLocalizedAt l)] ℚ :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton ↥(GaloisRep.ratLocalizedAt l) (K →ₗ[ℤ] ℚ) ψ.toLinearMap)
  have hLtmul : ∀ (s : ↥(GaloisRep.ratLocalizedAt l)) (k' : K),
      L (s ⊗ₜ[ℤ] k') = s • ψ k' := by
    intro s k'
    simp [L, LinearMap.toSpanSingleton_apply]
  have hrange : LinearMap.range L
      = Submodule.span ↥(GaloisRep.ratLocalizedAt l) (Set.range ⇑ψ) := by
    apply le_antisymm
    · rintro x ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul s k' =>
          rw [hLtmul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k', rfl⟩)
      | add t₁ t₂ h₁ h₂ =>
          rw [map_add]
          exact Submodule.add_mem _ h₁ h₂
    · rw [Submodule.span_le]
      rintro x ⟨k', rfl⟩
      exact ⟨(1 : ↥(GaloisRep.ratLocalizedAt l)) ⊗ₜ[ℤ] k', by rw [hLtmul]; simp⟩
  have hcl : (Submonoid.closure (Set.range ⇑ψ) : Set ℚ) = Set.range ⇑ψ := by
    apply Set.Subset.antisymm
    · intro x hx
      induction hx using Submonoid.closure_induction with
      | mem y hy => exact hy
      | one => exact ⟨1, map_one ψ⟩
      | mul y z _ _ hy hz =>
          obtain ⟨a, rfl⟩ := hy
          obtain ⟨b, rfl⟩ := hz
          exact ⟨a * b, map_mul ψ a b⟩
    · exact Submonoid.subset_closure
  have hadj : Subalgebra.toSubmodule
      (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt l) (Set.range ⇑ψ))
      = Submodule.span ↥(GaloisRep.ratLocalizedAt l) (Set.range ⇑ψ) := by
    rw [Algebra.adjoin_eq_span, hcl]
  rw [hadj, ← hrange, LinearMap.range_eq_map]
  exact hfin.fg_top.map L

theorem exists_rat_of_forall_fixed {x : AlgebraicClosure ℚ}
    (hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ x = x) :
    ∃ q : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) q = x :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix

def counitPoint (K : Type) [CommRing K] [HopfAlgebra ℤ K] (L : Type) [CommRing L] [Algebra ℤ L] :
    K →ₐ[ℤ] L :=
  (Algebra.ofId ℤ L).comp (Bialgebra.counitAlgHom ℤ K)

theorem comp_counitPoint_galois (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars ℤ).comp
      (counitPoint K (AlgebraicClosure ℚ)) = counitPoint K (AlgebraicClosure ℚ) := by
  ext k
  simp [counitPoint]

theorem exists_rat_point_apply (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (φ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K) :
    ∃ q : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) q = φ k := by
  apply exists_rat_of_forall_fixed
  intro σ
  have key : ((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars ℤ).comp φ = φ := by
    rcases eq_or_ne φ (counitPoint K (AlgebraicClosure ℚ)) with rfl | hne
    · exact comp_counitPoint_galois K σ
    · obtain ⟨y, hy_ne, huniq⟩ :=
        (Nat.card_eq_two_iff' (counitPoint K (AlgebraicClosure ℚ))).mp hgen
      have h1 : ((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars ℤ).comp φ ≠
          counitPoint K (AlgebraicClosure ℚ) := by
        intro h
        apply hne
        have h2 := congrArg
          (fun ρ => (((σ.symm : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars ℤ).comp ρ)) h
        rw [← AlgHom.comp_assoc] at h2
        have h3 : ((σ.symm : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars ℤ).comp
            ((σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars ℤ) =
            AlgHom.id ℤ (AlgebraicClosure ℚ) := by
          ext z
          simp
        rw [h3, AlgHom.id_comp] at h2
        rw [h2]
        exact comp_counitPoint_galois K σ.symm
      rw [huniq _ h1, huniq _ hne]
  have := congrArg (fun ρ : K →ₐ[ℤ] AlgebraicClosure ℚ => ρ k) key
  simpa using this

theorem exists_ratAlgHom (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (φ : K →ₐ[ℤ] AlgebraicClosure ℚ)
    (h : ∀ k, ∃ q : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) q = φ k) :
    ∃ ψ : K →ₐ[ℤ] ℚ, ∀ k, algebraMap ℚ (AlgebraicClosure ℚ) (ψ k) = φ k := by
  choose g hg using h
  have hinj : Function.Injective (algebraMap ℚ (AlgebraicClosure ℚ)) :=
    (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  refine ⟨{ toFun := g
            map_one' := hinj (by rw [hg, map_one, map_one])
            map_mul' := fun a b => hinj (by simp only [map_mul, hg])
            map_zero' := hinj (by rw [hg, map_zero, map_zero])
            map_add' := fun a b => hinj (by simp only [map_add, hg])
            commutes' := fun n => hinj (by rw [hg, AlgHom.commutes]; simp) }, hg⟩

theorem den_eq_one (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (hff : ∀ l : ℕ, l.Prime → l ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt l) (TensorProduct ℤ (GaloisRep.ratLocalizedAt l) K))
    (ψ : K →ₐ[ℤ] ℚ)
    (hψA : ∀ k, algebraMap ℚ (AlgebraicClosure ℚ) (ψ k) ∈ A) (k : K) :
    (ψ k).den = 1 := by
  by_contra hne
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
  rcases eq_or_ne q p with hqp | hqp
  ·
    subst hqp
    set x : ℚ := ψ k with hxdef
    set j := algebraMap ℚ (AlgebraicClosure ℚ) with hj
    have hyA : j x ∈ A := hψA k
    obtain ⟨d', hd'⟩ := hq_dvd
    have hcop : IsCoprime x.num (x.den : ℤ) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd, Int.natAbs_natCast] using x.reduced)
    obtain ⟨u, v, huv⟩ := hcop
    have hdq : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_pos x).ne'
    have hnum : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff hdq).mp (Rat.num_div_den x)
    have E1 : ((x.num : ℤ) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) *
        (d' : AlgebraicClosure ℚ) * j x := by
      calc ((x.num : ℤ) : AlgebraicClosure ℚ) = j ((x.num : ℚ)) := by
            rw [map_intCast]
        _ = j (x * (x.den : ℚ)) := by rw [← hnum]
        _ = j x * ((x.den : ℕ) : AlgebraicClosure ℚ) := by
            rw [map_mul, map_natCast]
        _ = (q : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ) * j x := by
            rw [hd']
            push_cast
            ring
    have E2 : (q : AlgebraicClosure ℚ) *
        ((u : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ) * j x +
          (v : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ)) = 1 := by
      have h1 : ((u * x.num + v * (x.den : ℤ) : ℤ) : AlgebraicClosure ℚ) = 1 := by
        rw [huv]; norm_num
      push_cast at h1
      calc (q : AlgebraicClosure ℚ) *
            ((u : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ) * j x +
              (v : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ))
          = (u : AlgebraicClosure ℚ) *
              ((q : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ) * j x) +
              (v : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ)) := by
            ring
        _ = (u : AlgebraicClosure ℚ) * ((x.num : ℤ) : AlgebraicClosure ℚ) +
              (v : AlgebraicClosure ℚ) * ((x.den : ℕ) : AlgebraicClosure ℚ) := by
            rw [← E1, hd']
            push_cast
            ring
        _ = 1 := h1
    have hqinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ =
        (u : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ) * j x +
          (v : AlgebraicClosure ℚ) * (d' : AlgebraicClosure ℚ) :=
      inv_eq_of_mul_eq_one_right E2
    have hmem : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      rw [hqinv]
      exact add_mem
        (mul_mem (mul_mem (intCast_mem A u) (natCast_mem A d')) hyA)
        (mul_mem (intCast_mem A v) (natCast_mem A d'))
    rcases (ValuationSubring.mem_nonunits_iff_or A).mp hA with h0 | hninv
    · exact (Nat.cast_ne_zero.mpr hq_prime.ne_zero) h0
    · exact hninv hmem
  ·
    have hcop := den_coprime_of_finite K q hq_prime (hff q hq_prime hqp) ψ k
    exact hq_prime.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hq_dvd dvd_rfl))

theorem natCard_algHom_int_eq (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (hff : ∀ l : ℕ, l.Prime → l ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt l) (TensorProduct ℤ (GaloisRep.ratLocalizedAt l) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2) :
    Nat.card (K →ₐ[ℤ] ℤ) = Nat.card (K →ₐ[ℤ] ↥A) := by
  have hAinj : Function.Injective (algebraMap ℤ ↥A) := by
    intro a b hab
    have := congrArg (A.subtype) hab
    exact Int.cast_injective this
  refine Nat.card_congr (Equiv.ofBijective
    (fun ψ => ((Algebra.ofId ℤ ↥A).comp ψ : K →ₐ[ℤ] ↥A)) ⟨?_, ?_⟩)
  · intro ψ₁ ψ₂ h
    ext k
    have := congrArg (fun ρ : K →ₐ[ℤ] ↥A => ρ k) h
    simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply] at this
    exact hAinj this
  · intro φA

    let φ : K →ₐ[ℤ] AlgebraicClosure ℚ := (A.subtype.toIntAlgHom).comp φA
    obtain ⟨ψ, hψ⟩ := exists_ratAlgHom K φ (exists_rat_point_apply K hgen φ)
    have hψA : ∀ k, algebraMap ℚ (AlgebraicClosure ℚ) (ψ k) ∈ A := by
      intro k
      rw [hψ k]
      exact (φA k).2
    have hden : ∀ k, (ψ k).den = 1 := den_eq_one p A hA K hff ψ hψA

    have hint : ∀ k, algebraMap ℚ (AlgebraicClosure ℚ) ((ψ k).num : ℚ) =
        algebraMap ℚ (AlgebraicClosure ℚ) (ψ k) := by
      intro k
      congr 1
      conv_rhs => rw [← Rat.num_div_den (ψ k)]
      rw [hden k]
      norm_num
    refine ⟨{ toFun := fun k => (ψ k).num
              map_one' := ?_
              map_mul' := ?_
              map_zero' := ?_
              map_add' := ?_
              commutes' := ?_ }, ?_⟩
    · have : (ψ 1) = 1 := map_one ψ
      rw [show ((1 : ℤ)) = (1 : ℚ).num from rfl]
      exact congrArg Rat.num this
    · intro a b
      have h1 : ψ (a * b) = ψ a * ψ b := map_mul ψ a b
      have : ((ψ (a*b)).num : ℚ) = ((ψ a).num : ℚ) * ((ψ b).num : ℚ) := by
        have e1 : ((ψ (a*b)).num : ℚ) = ψ (a*b) := by
          conv_rhs => rw [← Rat.num_div_den (ψ (a*b))]
          rw [hden]; norm_num
        have e2 : ((ψ a).num : ℚ) = ψ a := by
          conv_rhs => rw [← Rat.num_div_den (ψ a)]
          rw [hden]; norm_num
        have e3 : ((ψ b).num : ℚ) = ψ b := by
          conv_rhs => rw [← Rat.num_div_den (ψ b)]
          rw [hden]; norm_num
        rw [e1, e2, e3, h1]
      exact_mod_cast this
    · have : (ψ 0) = 0 := map_zero ψ
      rw [show ((0 : ℤ)) = (0 : ℚ).num from rfl]
      exact congrArg Rat.num this
    · intro a b
      have h1 : ψ (a + b) = ψ a + ψ b := map_add ψ a b
      have : ((ψ (a+b)).num : ℚ) = ((ψ a).num : ℚ) + ((ψ b).num : ℚ) := by
        have e1 : ((ψ (a+b)).num : ℚ) = ψ (a+b) := by
          conv_rhs => rw [← Rat.num_div_den (ψ (a+b))]
          rw [hden]; norm_num
        have e2 : ((ψ a).num : ℚ) = ψ a := by
          conv_rhs => rw [← Rat.num_div_den (ψ a)]
          rw [hden]; norm_num
        have e3 : ((ψ b).num : ℚ) = ψ b := by
          conv_rhs => rw [← Rat.num_div_den (ψ b)]
          rw [hden]; norm_num
        rw [e1, e2, e3, h1]
      exact_mod_cast this
    · intro n
      have h1 : ψ (algebraMap ℤ K n) = algebraMap ℤ ℚ n := ψ.commutes n
      have : ((ψ (algebraMap ℤ K n)).num : ℚ) = ((n : ℤ) : ℚ) := by
        have e1 : ((ψ (algebraMap ℤ K n)).num : ℚ) = ψ (algebraMap ℤ K n) := by
          conv_rhs => rw [← Rat.num_div_den (ψ (algebraMap ℤ K n))]
          rw [hden]; norm_num
        rw [e1, h1]
        simp
      exact_mod_cast this
    ·
      ext k
      simp only [AlgHom.coe_comp, Function.comp_apply, Algebra.ofId_apply]
      have h1 : ((algebraMap ℤ ↥A ((ψ k).num) : ↥A) : AlgebraicClosure ℚ) =
          (((ψ k).num : ℤ) : AlgebraicClosure ℚ) := by
        simp
      show ((algebraMap ℤ ↥A ((ψ k).num) : ↥A) : AlgebraicClosure ℚ) = _
      rw [h1]
      have h2 : (((ψ k).num : ℤ) : AlgebraicClosure ℚ) =
          algebraMap ℚ (AlgebraicClosure ℚ) ((ψ k).num : ℚ) := by
        rw [map_intCast]
      rw [h2, hint k, hψ k]
      rfl

end ETABLEDM

namespace ETABLEDN

def specIntGlobalSectionsRingEquiv :
    Γ((fppfTerminal specInt).left, ⊤) ≃+* ℤ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv

def specIntGlobalSectionsAlgEquiv :
    Γ((fppfTerminal specInt).left, ⊤) ≃ₐ[ℤ] ℤ :=
  AlgEquiv.ofRingEquiv (f := specIntGlobalSectionsRingEquiv) fun n => by
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    exact map_intCast _ n

theorem natCard_fppfCohomology_zero_eq_natCard_algHom_int
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)))) :
    Nat.card (fppfCohomology specInt M 0) = Nat.card (K →ₐ[ℤ] ℤ) := calc
  Nat.card (fppfCohomology specInt M 0)
      = Nat.card (M.1.obj (Opposite.op (fppfTerminal specInt))) :=
    Nat.card_congr (fppfCohomologyZeroAddEquiv specInt M).toEquiv
  _ = Nat.card (Additive (WithConv (K →ₐ[ℤ] Γ((fppfTerminal specInt).left, ⊤)))) :=
    Nat.card_congr (e (fppfTerminal specInt)).toEquiv
  _ = Nat.card (K →ₐ[ℤ] Γ((fppfTerminal specInt).left, ⊤)) :=
    (Nat.card_congr (Additive.toMul.trans (WithConv.equiv _)))
  _ = Nat.card (K →ₐ[ℤ] ℤ) :=
    Nat.card_congr (AlgEquiv.arrowCongr AlgEquiv.refl specIntGlobalSectionsAlgEquiv)

theorem algHom_postcomp_subtype_injective (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Function.Injective
      (fun φ : K →ₐ[ℤ] ↥A => A.subtype.toIntAlgHom.comp φ) := by
  intro φ ψ h
  ext k
  exact congrArg (· k) (congrArg DFunLike.coe h)

theorem t_le_one (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (t : ℕ) (ht : Nat.card (K →ₐ[ℤ] ↥A) = 2 ^ t) : t ≤ 1 := by
  have hcard : Nat.card (K →ₐ[ℤ] ↥A) ≤ Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) := by
    haveI : Finite (K →ₐ[ℤ] AlgebraicClosure ℚ) := Nat.finite_of_card_ne_zero (by omega)
    exact Nat.card_le_card_of_injective _ (algHom_postcomp_subtype_injective K A)
  rw [ht, hgen, show (2 : ℕ) = 2 ^ 1 from rfl] at hcard
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp hcard

end ETABLEDN

namespace ETABLEDN3

theorem h1_half
    (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (enat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (M.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (t a : ℕ)
    (ha : Nat.card (K →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a)
    (h0M : Nat.card (fppfCohomology specInt M 0) = 2 ^ t) (ht1 : t ≤ 1) :
    ∃ l1 : ℕ, Nat.card (fppfCohomology specInt M 1) = 2 ^ l1 ∧ l1 + a ≤ 1 := by
  have _ := A
  rcases ModularCurve.iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
      p K M e enat hff hgen a ha with ⟨ha1, ⟨eL⟩⟩ | ⟨ha0, ⟨eL⟩⟩ | ⟨l1, h1, hl1⟩
  ·
    obtain ⟨-, h1⟩ :=
      AlgebraicGeometry.natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction _ M eL
    haveI := AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime 2
    haveI : Nonempty (FppfCohomologyLES.FppfH (FppfKummerSES.sheafULift.{0}.obj
        (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)) 1) := ⟨0⟩
    refine ⟨0, ?_, by omega⟩
    rw [h1, Nat.card_unique, pow_zero]
  ·
    obtain ⟨h0, h1⟩ :=
      AlgebraicGeometry.natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction _ M eL
    have hmu := AlgebraicGeometry.fppf_natCard_H1_muP_eq_natCard_H0_muP_of_pic_trivial 2
      two_ne_zero AlgebraicGeometry.natCard_fppfH1_Gm_specZ_eq_one
    refine ⟨t, ?_, by omega⟩
    rw [h1, hmu, ← h0, h0M]
  · exact ⟨l1, h1, hl1⟩

end ETABLEDN3

theorem solution
    (p : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (M : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf,
      M.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))
    (enat : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : M.1.obj (Opposite.op V)) (k : K),
      (Additive.toMul (e U (M.1.map f.op s))) k
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k))
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgen : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = 2)
    (t a : ℕ)
    (ht : Nat.card (K →ₐ[ℤ] ↥A) = 2 ^ t)
    (ha : Nat.card (K →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a) :
    ∃ l0 l1 : ℕ,
      Nat.card (fppfCohomology specInt M 0) = 2 ^ l0 ∧
      Nat.card (fppfCohomology specInt M 1) = 2 ^ l1 ∧
      t ≤ l0 ∧ l1 + a ≤ 1 := by
  have h0M : Nat.card (fppfCohomology specInt M 0) = 2 ^ t := by
    rw [ETABLEDN.natCard_fppfCohomology_zero_eq_natCard_algHom_int K M e,
      ETABLEDM.natCard_algHom_int_eq p A hA K hff hgen]
    exact ht
  have ht1 : t ≤ 1 := ETABLEDN.t_le_one K A hgen t ht
  obtain ⟨l1, h1, hl1⟩ := ETABLEDN3.h1_half p A K M e enat hff hgen t a ha h0M ht1
  exact ⟨t, l1, h0M, h1, le_rfl, hl1⟩

end

end S_ModularCurve_exists_natCard_fppfCohomology_of_sectionsEquiv_algHom_two
end P2MW
export P2MW.S_ModularCurve_exists_natCard_fppfCohomology_of_sectionsEquiv_algHom_two (solution)
