-- Prove2me | solution 1 for ModularCurve.mem_map_proj_multiplicativeSubmodule_iff_inertia_cyclotomic_and_map_proj_le_finPts_of_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8ac7616b-354b-5762-be2e-30f3d426c22b

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_map_proj_multiplicativeSubmodule_iff_inertia_cyclotomic_and_map_proj_le_finPts_of_ordinary

set_option autoImplicit false

namespace NineBAux

open scoped TensorProduct

theorem map_smul_of_adjoin_eq_top {p : ℕ} [Fact p.Prime] {𝕋 T : Type*} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋]
    [AddCommGroup T] [Module ℤ_[p] T] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]
    {ι : Type*} (op : ι → 𝕋) (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (R : T →ₗ[ℤ_[p]] T) (hR : ∀ (i : ι) (x : T), R (op i • x) = op i • R x) :
    ∀ (t : 𝕋) (x : T), R (t • x) = t • R x := by
  intro t
  have ht : t ∈ Algebra.adjoin ℤ_[p] (Set.range op) := by rw [hgen]; exact Algebra.mem_top
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨i, rfl⟩ x
    exact hR i x
  · intro r x
    rw [algebraMap_smul, algebraMap_smul, map_smul]
  · intro a b _ _ ha hb x
    rw [add_smul, map_add, ha, hb, add_smul]
  · intro a b _ _ ha hb x
    rw [mul_smul, ha, hb, mul_smul]

theorem isUnit_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : IsUnit ((2 : ℤ) : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  apply le_antisymm (PadicInt.norm_le_one _)
  by_contra h
  rw [not_le] at h
  have hdvd : (p : ℤ) ∣ 2 := (PadicInt.norm_int_lt_one_iff_dvd 2).mp h
  have : p ∣ 2 := by exact_mod_cast hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

end NineBAux

open ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hinertF : ∀ (m : ℕ), 0 < m → ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) m, σ • x - x ∈ O.finPts m)

    (hordI : ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ σ' ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ModularCurve.JH.tateGaloisRep M H p σ' (ModularCurve.JH.tateGaloisRep M H p σ x - x) =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ'.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) •
            (ModularCurve.JH.tateGaloisRep M H p σ x - x)) :

    (∀ x : ModularCurve.JH M H,
      x ∈ (P0.toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ↔
        x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
              (TateModule.proj p (ModularCurve.JH M H) 1) ∧
          ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
            (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • x = c • x) ∧

    ((P0.toAddSubgroup).map (TateModule.proj p (ModularCurve.JH M H) 1) ≤ O.finPts p) := by
  classical
  have hpr : p.Prime := Fact.out

  have hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : 𝕋) (x : TateModule p (ModularCurve.JH M H)),
      ModularCurve.JH.tateGaloisRep M H p σ (t • x) = t • ModularCurve.JH.tateGaloisRep M H p σ x := by
    intro σ
    refine NineBAux.map_smul_of_adjoin_eq_top op hgen (ModularCurve.JH.tateGaloisRep M H p σ) fun g x => ?_
    rw [hop, hop]
    apply Subtype.ext
    funext n
    show σ • ModularCurve.genOpH M H S g ((x : ℕ → ModularCurve.JH M H) n) =
      ModularCurve.genOpH M H S g (σ • (x : ℕ → ModularCurve.JH M H) n)
    exact ModularCurve.galois_smul_genOpH_comm M H S σ g _
  have hmemC : ∀ x : TateModule p (ModularCurve.JH M H),
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ↔ (S'.e i₀) • x = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      show S'.e i₀ • (S'.e i₀ • y) = S'.e i₀ • y
      rw [← mul_smul, (S'.coi.idem i₀).eq]
    · intro hx
      exact LinearMap.mem_range.mpr ⟨x, hx⟩
  have hstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ModularCurve.JH.tateGaloisRep M H p σ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) := by
    intro σ x hx
    rw [hmemC] at hx ⊢
    rw [← hcomm, hx]

  obtain ⟨σ₀, hσ₀I, hσ₀⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq Pl hPl (-1 : ℤ_[p]ˣ)
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[p], u = ((-1 : ℤ_[p]ˣ) : ℤ_[p]) := ⟨_, rfl⟩
  have hu1 : u - 1 = ((-2 : ℤ) : ℤ_[p]) := by rw [hu, Units.val_neg, Units.val_one]; norm_num
  obtain ⟨v, hv⟩ : ∃ v : ℤ_[p], v * (u - 1) = 1 := by
    rw [hu1]
    have h2 : IsUnit ((-2 : ℤ) : ℤ_[p]) := by
      have := (NineBAux.isUnit_two hp2).neg
      rwa [← Int.cast_neg] at this
    exact ⟨((h2.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), h2.val_inv_mul⟩

  have hP0Z : ∀ (r : ℤ_[p]), ∀ w ∈ P0, r • w ∈ P0 := fun r w hw => by
    rw [← algebraMap_smul 𝕋 r w]
    exact P0.smul_mem _ hw
  have hP0σ₀ : ∀ w ∈ P0, ModularCurve.JH.tateGaloisRep M H p σ₀ w = u • w := fun w hw => by
    rw [((hP0 w).mp hw).2 σ₀ hσ₀I, hσ₀, hu]

  have hdec : ∀ y ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
      ∃ y0 ∈ P0, ModularCurve.JH.tateGaloisRep M H p σ₀ (y - y0) = y - y0 := by
    intro y hy
    obtain ⟨z, hz⟩ : ∃ z, z = ModularCurve.JH.tateGaloisRep M H p σ₀ y - y := ⟨_, rfl⟩
    have hzP0 : z ∈ P0 := by
      rw [hz, hP0]
      refine ⟨Submodule.sub_mem _ (hstab σ₀ y hy) hy, fun σ' hσ' => ?_⟩
      exact hordI σ₀ hσ₀I σ' hσ' y hy
    refine ⟨v • z, hP0Z v z hzP0, ?_⟩
    have hRz : ModularCurve.JH.tateGaloisRep M H p σ₀ z = u • z := hP0σ₀ z hzP0
    rw [map_sub, map_smul, hRz, smul_smul]
    have hy' : ModularCurve.JH.tateGaloisRep M H p σ₀ y = y + z := by rw [hz]; abel
    rw [hy']
    have : (v * u) • z = z + v • z := by
      have h1 : v * u = 1 + v := by linear_combination hv
      rw [h1]
      calc ((1 : ℤ_[p]) + v) • z = (1 : ℤ_[p]) • z + v • z := add_smul 1 v z
        _ = z + v • z := by rw [one_smul]
    rw [this]
    abel

  have L1 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : TateModule p (ModularCurve.JH M H)),
      TateModule.proj p (ModularCurve.JH M H) 1 (ModularCurve.JH.tateGaloisRep M H p σ x) =
        σ • TateModule.proj p (ModularCurve.JH M H) 1 x := fun σ x => rfl
  have L2 : ∀ (r : ℤ_[p]) (x : TateModule p (ModularCurve.JH M H)),
      TateModule.proj p (ModularCurve.JH M H) 1 (r • x) = ((r.appr 1 : ℕ) : ℤ) • TateModule.proj p (ModularCurve.JH M H) 1 x :=
    fun r x => TateModule.smul_apply r x 1
  have L3 : ∀ x : TateModule p (ModularCurve.JH M H), ((p ^ 1 : ℕ) : ℤ) • TateModule.proj p (ModularCurve.JH M H) 1 x = 0 :=
    fun x => TateModule.torsionBy_proj 1 x

  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hpr.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hexp : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) →
      ((c : ℕ) : ZMod (p ^ 1)) = (((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr 1 : ZMod (p ^ 1)) := by
    intro σ c hc
    have h1 := hc ζ₀ hζ₀.pow_eq_one
    have h2 := cyclotomicCharacter.spec p (n := 1) σ.toRingEquiv ζ₀ (by rw [pow_one]; exact hζ₀.pow_eq_one)
    have h12 : ζ₀ ^ c = ζ₀ ^ ((PadicInt.toZModPow 1)
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val := by
      rw [← h1]; exact h2
    have hmodpow : ∀ n : ℕ, ζ₀ ^ (n % p) = ζ₀ ^ n := fun n => by
      conv_rhs => rw [← Nat.mod_add_div n p]
      rw [pow_add, pow_mul, hζ₀.pow_eq_one, one_pow, mul_one]
    have hmod : c ≡ ((PadicInt.toZModPow 1)
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val [MOD p] :=
      hζ₀.pow_inj (Nat.mod_lt _ hpr.pos) (Nat.mod_lt _ hpr.pos) (by rw [hmodpow, hmodpow, h12])
    rw [← TateModule.toZModPow_eq_appr, ← ZMod.natCast_zmod_val ((PadicInt.toZModPow 1) _)]
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mpr ?_
    have hp1 : p ^ 1 = p := pow_one p
    unfold Nat.ModEq at hmod ⊢
    simp only [hp1]
    exact hmod
  have L4 : ∀ w ∈ P0, ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) →
        σ • TateModule.proj p (ModularCurve.JH M H) 1 w = c • TateModule.proj p (ModularCurve.JH M H) 1 w := by
    intro w hw σ hσ c hc
    rw [← L1, ((hP0 w).mp hw).2 σ hσ, L2, ← natCast_zsmul]
    exact (TateModule.natCast_smul_eq_of_zmod_eq (L3 w) (hexp σ c hc)).symm

  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, c₀ = ((PadicInt.toZModPow 1) ((-1 : ℤ_[p]ˣ) : ℤ_[p])).val := ⟨_, rfl⟩
  have hσ₀ζ : ∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ₀ ζ = ζ ^ c₀ := by
    intro ζ hζ
    have h := cyclotomicCharacter.spec p (n := 1) σ₀.toRingEquiv ζ (by rw [pow_one]; exact hζ)
    rw [hσ₀, ← hc₀] at h
    exact h
  have hc1 : p ∣ c₀ + 1 := by
    have h0 : ((c₀ + 1 : ℕ) : ZMod (p ^ 1)) = 0 := by
      rw [Nat.cast_add, Nat.cast_one, hc₀, ZMod.natCast_zmod_val, Units.val_neg, Units.val_one, map_neg, map_one,
        neg_add_cancel]
    have := (ZMod.natCast_eq_zero_iff _ _).1 h0
    rwa [pow_one] at this
  have hndvd : ¬ (p : ℤ) ∣ ((c₀ : ℤ) - 1) := by
    intro h
    have h1 : (p : ℤ) ∣ ((c₀ : ℤ) + 1) := by exact_mod_cast hc1
    have h2 : (p : ℤ) ∣ 2 := by
      have := Int.dvd_sub h1 h
      rwa [show ((c₀ : ℤ) + 1) - ((c₀ : ℤ) - 1) = 2 by ring] at this
    have h3 : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h3)
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) ((c₀ : ℤ) - 1) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hpr).irreducible).2 hndvd
  have hkill : ∀ x1 : ModularCurve.JH M H, (p : ℤ) • x1 = 0 → x1 = c₀ • x1 → x1 = 0 := by
    intro x1 hp hσ
    have hc : ((c₀ : ℤ) - 1) • x1 = 0 := by
      rw [sub_zsmul, one_zsmul, natCast_zsmul, ← hσ]
      abel
    calc x1 = (1 : ℤ) • x1 := (one_zsmul x1).symm
      _ = (a * (p : ℤ) + b * ((c₀ : ℤ) - 1)) • x1 := by rw [hab]
      _ = a • ((p : ℤ) • x1) + b • (((c₀ : ℤ) - 1) • x1) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hp, hc, zsmul_zero, zsmul_zero, add_zero]
  have Lp : ∀ x : TateModule p (ModularCurve.JH M H), (p : ℤ) • TateModule.proj p (ModularCurve.JH M H) 1 x = 0 := by
    intro x
    have := L3 x
    rwa [pow_one] at this
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩

  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ P0 := hw
    refine ⟨⟨w, ?_, rfl⟩, fun σ hσ c hc => L4 w hw' σ hσ c hc⟩
    exact ((hP0 w).mp hw').1

  · rintro ⟨⟨y, hy, rfl⟩, hcyc⟩
    have hy' : y ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) := hy
    obtain ⟨y0, hy0, hfix⟩ := hdec y hy'
    have hsplit : TateModule.proj p (ModularCurve.JH M H) 1 y =
        TateModule.proj p (ModularCurve.JH M H) 1 y0 + TateModule.proj p (ModularCurve.JH M H) 1 (y - y0) := by
      rw [map_sub]; abel
    obtain ⟨x1, hx1⟩ : ∃ x1, x1 = TateModule.proj p (ModularCurve.JH M H) 1 (y - y0) := ⟨_, rfl⟩
    rw [← hx1] at hsplit
    have hx1fix : σ₀ • x1 = x1 := by rw [hx1, ← L1, hfix]
    have hx0 : σ₀ • TateModule.proj p (ModularCurve.JH M H) 1 y0 = c₀ • TateModule.proj p (ModularCurve.JH M H) 1 y0 :=
      L4 y0 hy0 σ₀ hσ₀I c₀ hσ₀ζ
    have hall := hcyc σ₀ hσ₀I c₀ hσ₀ζ
    have h1 : σ₀ • (TateModule.proj p (ModularCurve.JH M H) 1 y0 + x1) = c₀ • TateModule.proj p (ModularCurve.JH M H) 1 y0 + x1 := by
      rw [smul_add, hx0, hx1fix]
    have h2 : c₀ • (TateModule.proj p (ModularCurve.JH M H) 1 y0 + x1) = c₀ • TateModule.proj p (ModularCurve.JH M H) 1 y0 + c₀ • x1 :=
      smul_add c₀ _ x1
    rw [hsplit, h1, h2, add_right_inj] at hall
    have hx1zero : x1 = 0 := hkill x1 (by rw [hx1]; exact Lp _) hall
    refine ⟨y0, hy0, ?_⟩
    rw [hsplit, hx1zero, add_zero]

  · rintro x ⟨w, hw, rfl⟩
    have hw' : w ∈ P0 := hw
    have hRw : ModularCurve.JH.tateGaloisRep M H p σ₀ w - w = (u - 1) • w := by
      rw [hP0σ₀ w hw']
      calc u • w - w = u • w - (1 : ℤ_[p]) • w := by rw [one_smul]
        _ = (u - 1) • w := (sub_smul u 1 w).symm
    have hweq : w = v • (ModularCurve.JH.tateGaloisRep M H p σ₀ w - w) := by
      rw [hRw, smul_smul, hv, one_smul]
    have hmem : σ₀ • TateModule.proj p (ModularCurve.JH M H) 1 w - TateModule.proj p (ModularCurve.JH M H) 1 w ∈ O.finPts p := by
      refine hinertF p hpr.pos σ₀ hσ₀I _ ?_
      rw [AlgebraicCurve.Pic0.mem_torsion]
      exact Lp w
    show TateModule.proj p (ModularCurve.JH M H) 1 w ∈ O.finPts p
    rw [hweq, L2, map_sub, L1]
    exact AddSubgroup.zsmul_mem _ hmem _

end S_ModularCurve_mem_map_proj_multiplicativeSubmodule_iff_inertia_cyclotomic_and_map_proj_le_finPts_of_ordinary
end P2MW
export P2MW.S_ModularCurve_mem_map_proj_multiplicativeSubmodule_iff_inertia_cyclotomic_and_map_proj_le_finPts_of_ordinary (solution)
