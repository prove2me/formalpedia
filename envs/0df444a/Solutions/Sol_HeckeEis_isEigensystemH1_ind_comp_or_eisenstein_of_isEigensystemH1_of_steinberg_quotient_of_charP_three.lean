-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4447167c-9db8-55f4-a848-a81fbe3960b7

import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2
import Theorems.Thm_CohCarrier_subsingleton_H2_gamma0_of_isUnit_index
import Theorems.Thm_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
import Theorems.Thm_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open CongruenceSubgroup CuspidalType
open scoped MatrixGroups

namespace K3a3Chi

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

abbrev red : ↥(Gamma0 N) →* CuspidalType.GL2 q :=
  ((Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype)

variable {κ : Type} [Field κ] {W : Type} [AddCommMonoid W] [Module κ W]

noncomputable abbrev adj (X : Representation κ (CuspidalType.GL2 q) W) (ℓ : ℕ) : W →ₗ[κ] W :=
  if h : ((ℓ : ZMod q) ≠ 0) then X (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id

theorem diag_mul_red_heckeConj (ℓ : ℕ) [NeZero ℓ] (hℓ : ((ℓ : ZMod q) ≠ 0)) (s : ↥(HeckeEis.heckeUpper N ℓ)) :
    CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) hℓ) * red N q (HeckeEis.heckeConj N ℓ s) =
      red N q (s : ↥(Gamma0 N)) * CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) hℓ) := by
  set D : CuspidalType.GL2 q := CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) hℓ) with hD
  have hint : !![(ℓ : ℤ), 0; 0, 1] * (((HeckeEis.heckeConj N ℓ s : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((s : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by
    have h01 : (ℓ : ℤ) * ((((s : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1) / (ℓ : ℤ)) = ((s : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 :=
      Int.mul_ediv_cancel' ((HeckeEis.mem_heckeUpper N ℓ).mp s.2)
    rw [HeckeEis.coe_heckeConj]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HeckeEis.heckeConjMat, Matrix.mul_apply, Fin.sum_univ_two, h01, mul_comm]
  apply Units.ext
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom (ZMod q))) hint
  rw [Matrix.map_mul, Matrix.map_mul] at this
  have hDm : ((D : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (!![(ℓ : ℤ), 0; 0, 1]).map (Int.castRingHom (ZMod q)) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hD, CuspidalType.diagElem]
  have h1 : ∀ x : ↥(Gamma0 N), ((red N q x : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      ((x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod q)) := fun x => rfl
  rw [Units.val_mul, Units.val_mul, hDm, h1, h1]
  exact this

theorem diagElem_comm (a b : (ZMod q)ˣ) : CuspidalType.diagElem q a * CuspidalType.diagElem q b =
    CuspidalType.diagElem q b * CuspidalType.diagElem q a := by
  apply Units.ext
  simp only [Units.val_mul, CuspidalType.diagElem_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem adj_compat (X : Representation κ (CuspidalType.GL2 q) W) (ℓ : ℕ) [NeZero ℓ] (hℓ : ((ℓ : ZMod q) ≠ 0))
    (s : ↥(HeckeEis.heckeUpper N ℓ)) :
    adj q X ℓ ∘ₗ (X.comp (red N q)) (HeckeEis.heckeConj N ℓ s) = (X.comp (red N q)) (s : ↥(Gamma0 N)) ∘ₗ adj q X ℓ := by
  simp only [adj, dif_pos hℓ]
  show X _ ∘ₗ X (red N q (HeckeEis.heckeConj N ℓ s)) = X (red N q (s : ↥(Gamma0 N))) ∘ₗ X _
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, diag_mul_red_heckeConj N q ℓ hℓ s]

theorem adj_comm (X : Representation κ (CuspidalType.GL2 q) W) (ℓ ℓ' : ℕ) :
    adj q X ℓ ∘ₗ adj q X ℓ' = adj q X ℓ' ∘ₗ adj q X ℓ := by
  simp only [adj]
  split_ifs with h h'
  · rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, diagElem_comm]
  · rfl
  · rfl
  · rfl

theorem natCast_ne_zero_of {S₀ : Set ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ insert q S₀) : ((ℓ : ZMod q) ≠ 0) := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hq : q.Prime := Fact.out
  have : ℓ = q := ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp h).symm
  exact hℓS (this ▸ Set.mem_insert q S₀)

theorem coeffSum_ind (g : CuspidalType.GL2 q) (f : CuspidalType.ProjLine q →₀ κ) :
    CuspidalType.coeffSum q κ (CuspidalType.ind q κ g f) = CuspidalType.coeffSum q κ f := by
  rw [CuspidalType.coeffSum, Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  rfl

theorem coeffSum_single (x : CuspidalType.ProjLine q) : CuspidalType.coeffSum q κ (Finsupp.single x 1) = 1 := by
  rw [CuspidalType.coeffSum, Finsupp.linearCombination_single, one_smul]

theorem exists_H (N ℓ₀ : ℕ) [NeZero N] (hℓ₀ : ℓ₀.Prime) :
    ∃ H : Subgroup (ZMod (N * ℓ₀))ˣ,
      (∀ u ∈ H, ZMod.castHom (dvd_mul_left ℓ₀ N) (ZMod ℓ₀) (u : ZMod (N * ℓ₀)) = 1) ∧ H.index = ℓ₀ - 1 := by
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩
  haveI : Fact ℓ₀.Prime := ⟨hℓ₀⟩
  let f : (ZMod (N * ℓ₀))ˣ →* (ZMod ℓ₀)ˣ := ZMod.unitsMap (dvd_mul_left ℓ₀ N)
  refine ⟨f.ker, fun u hu => ?_, ?_⟩
  · have := congrArg (fun x : (ZMod ℓ₀)ˣ => (x : ZMod ℓ₀)) (MonoidHom.mem_ker.mp hu)
    simpa [f, ZMod.unitsMap] using this
  · rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (dvd_mul_left ℓ₀ N)),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hℓ₀]

theorem subsingleton_H2 (N ℓ₀ : ℕ) [NeZero N] (hℓ₀ : ℓ₀.Prime) (h5 : 5 ≤ ℓ₀) (hmod : ℓ₀ % 3 = 2) [CharP κ 3]
    (A : Rep κ ↥(Gamma0 (N * ℓ₀))) : Subsingleton (groupCohomology A 2) := by
  haveI : NeZero (N * ℓ₀) := ⟨Nat.mul_ne_zero (NeZero.ne N) hℓ₀.ne_zero⟩
  obtain ⟨H, hH, hidx⟩ := exists_H N ℓ₀ hℓ₀
  refine CohCarrier.subsingleton_H2_gamma0_of_isUnit_index (N * ℓ₀) ℓ₀ (dvd_mul_left ℓ₀ N) (by omega) H hH ?_ A
  rw [hidx]

  have h3 : ((ℓ₀ - 1 : ℕ) : κ) = 1 := by
    have : (ℓ₀ - 1) % 3 = 1 := by omega
    have h3κ : (3 : κ) = 0 := by exact_mod_cast CharP.cast_eq_zero κ 3
    rw [← Nat.div_add_mod (ℓ₀ - 1) 3, this]
    push_cast
    rw [h3κ, zero_mul, zero_add]
  rw [h3]; exact isUnit_one

theorem main (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ) (hS₀ : S₀.Finite)
    (κ : Type) [Field κ] [CharP κ 3] (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ) (n : ℕ → ℤ) (hlam : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (n ℓ : κ))
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp (red N q)) (fun ℓ : ℕ => adj q ρ ℓ) (insert q S₀) lam) :
    HeckeEis.IsEigensystemH1 N ((CuspidalType.ind q κ).comp (red N q)) (fun ℓ : ℕ => adj q (CuspidalType.ind q κ) ℓ) (insert q S₀) lam ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by
  classical

  let S : Set ℕ := insert q S₀ ∪ {ℓ | ℓ ∣ N} ∪ {ℓ | ℓ < 5}
  have hSfin : S.Finite := by
    refine ((hS₀.insert q).union ?_).union (Set.finite_lt_nat 5)
    exact (Set.finite_le_nat N).subset fun ℓ (hℓ : ℓ ∣ N) => Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hℓ
  by_cases hex : ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ℓ₀ % 3 = 2 ∧ lam ℓ₀ ≠ 0
  ·
    obtain ⟨ℓ₀, hℓ₀, hℓ₀S, hmod, hlam0⟩ := hex
    have hℓ₀N : ¬ ℓ₀ ∣ N := fun h => hℓ₀S (Or.inl (Or.inr h))
    have hℓ₀S₀ : ℓ₀ ∉ insert q S₀ := fun h => hℓ₀S (Or.inl (Or.inl h))
    have h5 : 5 ≤ ℓ₀ := by
      by_contra h; exact hℓ₀S (Or.inr (by simpa using h))

    have devissage : ∀ {U : Type} [AddCommGroup U] [Module κ U] [FiniteDimensional κ U]
        (X : Representation κ (CuspidalType.GL2 q) U)
        (ιU : U →ₗ[κ] (CuspidalType.ProjLine q →₀ κ))
        (hιU : ∀ (g : CuspidalType.GL2 q) (w : U), ιU (X g w) = CuspidalType.ind q κ g (ιU w))
        (hinj : Function.Injective ιU)
        (hrange : ∀ f : CuspidalType.ProjLine q →₀ κ, f ∈ LinearMap.range ιU ↔ CuspidalType.coeffSum q κ f = 0)
        (π' : U →ₗ[κ] V) (hπ' : ∀ (g : CuspidalType.GL2 q) (w : U), π' (X g w) = ρ g (π' w))
        (hπ'surj : Function.Surjective π'),
        HeckeEis.IsEigensystemH1 N ((CuspidalType.ind q κ).comp (red N q)) (fun ℓ : ℕ => adj q (CuspidalType.ind q κ) ℓ)
            (insert q S₀) lam ∨
          ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by
      intro U _ _ _ X ιU hιU hinj hrange π' hπ' hπ'surj

      have hU : HeckeEis.IsEigensystemH1 N (X.comp (red N q)) (fun ℓ : ℕ => adj q X ℓ) (insert q S₀) lam := by
        refine HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective_of_subsingleton_H2 N (insert q S₀)
          (X.comp (red N q)) (ρ.comp (red N q)) (fun ℓ => adj q X ℓ) (fun ℓ => adj q ρ ℓ)
          (fun ℓ _ hℓ hℓN hℓS s => adj_compat N q X ℓ (natCast_ne_zero_of q hℓ hℓS) s)
          (fun ℓ ℓ' _ _ _ _ _ _ => adj_comm q X ℓ ℓ') π' ?_ ?_ hπ'surj ℓ₀ hℓ₀ hℓ₀N hℓ₀S₀
          (fun A => subsingleton_H2 (κ := κ) N ℓ₀ hℓ₀ h5 hmod A) lam hlam0 hocc
        · intro g
          apply LinearMap.ext; intro v
          exact hπ' (red N q g) v
        · intro ℓ _ _ _
          apply LinearMap.ext; intro v
          simp only [adj, LinearMap.comp_apply]
          split_ifs with h
          · exact hπ' _ v
          · rfl

      let x₀ : CuspidalType.ProjLine q := Projectivization.mk (ZMod q) ![0, 1] (by simp)
      let q₀ : CuspidalType.ProjLine q →₀ κ := Finsupp.single x₀ 1
      have hpush := HeckeEis.isEigensystemH1_or_of_isEigensystemH1_of_injective N (insert q S₀)
        (X.comp (red N q)) ((CuspidalType.ind q κ).comp (red N q)) (fun ℓ => adj q X ℓ) (fun ℓ => adj q (CuspidalType.ind q κ) ℓ)
        (fun ℓ _ hℓ hℓN hℓS s => adj_compat N q (CuspidalType.ind q κ) ℓ (natCast_ne_zero_of q hℓ hℓS) s)
        ιU (fun g => LinearMap.ext fun w => hιU (red N q g) w) (fun ℓ _ _ _ => by
          apply LinearMap.ext; intro v
          simp only [adj, LinearMap.comp_apply]
          split_ifs with h
          · exact hιU _ v
          · rfl)
        hinj q₀
        (fun v _ => ⟨CuspidalType.coeffSum q κ v, by
          rw [hrange, map_sub, map_smul, coeffSum_single, smul_eq_mul, mul_one, sub_self]⟩)
        (fun _ => 1)
        (fun ℓ _ _ _ => by
          rw [hrange, map_sub, one_smul]
          simp only [adj]
          split_ifs with h
          · rw [coeffSum_ind, sub_self]
          · rw [LinearMap.id_apply, sub_self])
        lam hU
      rcases hpush with hL | ⟨-, hR⟩
      · exact Or.inl hL
      · exact Or.inr fun ℓ hℓ hℓN hℓS => by rw [hR ℓ hℓ hℓN hℓS, mul_one]
    haveI : Module.Finite κ (CuspidalType.ProjLine q →₀ κ) := Module.Finite.finsupp
    exact devissage (CuspidalType.steinberg q κ).toRepresentation
      (CuspidalType.steinberg q κ).toSubmodule.subtype (fun g w => rfl) Subtype.val_injective
      (fun f => by rw [Submodule.range_subtype]; exact LinearMap.mem_ker) π (fun g w => hπ g w) hπsurj
  ·
    exfalso
    push Not at hex
    refine ResidualGaloisRep.exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two k ρbar n S hSfin
      ?_ ?_ h3
    · intro ℓ hℓ hℓS A hA σ hσ
      have hℓN : ¬ ℓ ∣ N := fun h => hℓS (Or.inl (Or.inr h))
      have hℓS₀ : ℓ ∉ insert q S₀ := fun h => hℓS (Or.inl (Or.inl h))
      have hℓ3 : ℓ ≠ 3 := by rintro rfl; exact hℓS (Or.inr (by norm_num))
      exact htr ℓ hℓ hℓN hℓS₀ hℓ3 A hA σ hσ
    · intro ℓ hℓ hℓS hmod
      have hℓN : ¬ ℓ ∣ N := fun h => hℓS (Or.inl (Or.inr h))
      have hℓS₀ : ℓ ∉ insert q S₀ := fun h => hℓS (Or.inl (Or.inl h))
      have h0 : lam ℓ = 0 := hex ℓ hℓ hℓS (by rw [Nat.ModEq] at hmod; simpa using hmod)
      rw [hlam ℓ hℓ hℓN hℓS₀] at h0

      rw [CharP.intCast_eq_zero_iff κ 3] at h0
      exact (CharP.intCast_eq_zero_iff k 3 (n ℓ)).mpr h0

end K3a3Chi

theorem solution
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ) (hS₀ : S₀.Finite)
    (κ : Type) [Field κ] [CharP κ 3] (hq1 : (q : κ) + 1 = 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ) (n : ℕ → ℤ) (hlam : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (n ℓ : κ))
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → ℓ ≠ 3 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    HeckeEis.IsEigensystemH1 N ((CuspidalType.ind q κ).comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
        (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then (CuspidalType.ind q κ) (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h))
        else LinearMap.id) (insert q S₀) lam ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 :=
  K3a3Chi.main N q hqN S₀ hS₀ κ hq1 ρ π hπ hπsurj hπker lam n hlam k ρbar hirr h3 htr hocc

end S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_ind_comp_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_charP_three (solution)
