-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_03
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T04:58:54.156591+00:00
-- url     : https://prove2.me/submissions/71d706ce-2d4b-42a7-b9ce-17d967ae27b1

import Definitions.Def_SidorenkoFiniteGeometryCertificates03
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0004]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0005]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0007]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0011]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0014]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0016]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0017]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0020]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0021]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0023]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0035]
  [p11 : OAI.SidorenkoCounterexample.ProofCertificate_0036]
  [p12 : OAI.SidorenkoCounterexample.ProofCertificate_0042]
  [p13 : OAI.SidorenkoCounterexample.ProofCertificate_0060]
  [p14 : OAI.SidorenkoCounterexample.ProofCertificate_0062]
  [p15 : OAI.SidorenkoCounterexample.ProofCertificate_0063]
  [p16 : OAI.SidorenkoCounterexample.ProofCertificate_0066]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Bounds
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
theorem certificate_proof_0069 (k : ℕ) (hk : k ≤ finrank K V) :
    (Fintype.card K : ℝ)^(k*(finrank K V-k)) ≤ Nat.card (DimSubspace K V k) := by
  rw [subspace_count_real k hk]
  let q : ℝ := Fintype.card K
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hq0 : 0 < q := by linarith
  have hfac (i : Fin k) : q^(finrank K V-k) ≤
      (q^finrank K V-q^i.val)/(q^k-q^i.val) := by
    have hd : 0 < q^k-q^i.val := sub_pos.mpr (pow_lt_pow_right₀ hq i.isLt)
    have hid : q^finrank K V = q^(finrank K V-k)*q^k := by
      rw [←pow_add,Nat.sub_add_cancel hk]
    apply (le_div_iff₀ hd).mpr
    rw [hid]
    have hp : 1 ≤ q^(finrank K V-k) := one_le_pow₀ hq.le
    have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hq0.le i.val)
    nlinarith
  calc
    q^(k*(finrank K V-k)) = ∏ _i : Fin k, q^(finrank K V-k) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
      rw [Nat.mul_comm]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => pow_nonneg hq0.le _) (fun i _ => hfac i)

private instance certificate_instance_0069 : OAI.SidorenkoCounterexample.ProofCertificate_0069 := by
  constructor
  intros
  apply @certificate_proof_0069 <;> assumption

end Bounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainingSubspaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0070 (S U : Submodule K V) (hS : S ≤ U) :
    finrank K (U.map S.mkQ) + finrank K S = finrank K U := by
  have h := LinearMap.finrank_range_add_finrank_ker (S.mkQ.comp U.subtype)
  rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.ker_comp,Submodule.ker_mkQ] at h
  rw [(Submodule.comapSubtypeEquivOfLe hS).finrank_eq] at h
  exact h

private instance certificate_instance_0070 : OAI.SidorenkoCounterexample.ProofCertificate_0070 := by
  constructor
  intros
  apply @certificate_proof_0070 <;> assumption

variable [Fintype K] [Finite V]
 omit [Finite V] in
theorem certificate_proof_0071 (S : Submodule K V) (r : ℕ)
    (hr : finrank K S ≤ r) (hrD : r ≤ finrank K V) :
    (Fintype.card K : ℝ)^((r-finrank K S)*(finrank K V-r)) ≤
        Nat.card {U : DimSubspace K V r // S ≤ U.val} ∧
    (Nat.card {U : DimSubspace K V r // S ≤ U.val} : ℝ) ≤
        2^r*(Fintype.card K : ℝ)^((r-finrank K S)*(finrank K V-r)) := by
  let : Finite (V ⧸ S) := Module.finite_of_finite K
  have hD := S.finrank_quotient_add_finrank
  have hle : r-finrank K S ≤ finrank K (V ⧸ S) := by omega
  have he : finrank K (V ⧸ S)-(r-finrank K S) = finrank K V-r := by omega
  rw [Nat.card_congr (containingSubspaceEquiv S r hr)]
  constructor
  · simpa only [he] using (subspace_count_lower (K := K) (V := V ⧸ S) (r-finrank K S) hle)
  · have h := subspace_count_upper (K := K) (V := V ⧸ S) (r-finrank K S) hle
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le r _)) (by positivity))

private instance certificate_instance_0071 : OAI.SidorenkoCounterexample.ProofCertificate_0071 := by
  constructor
  intros
  apply @certificate_proof_0071 <;> assumption

end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
theorem certificate_proof_0072 (L M N : Submodule K V) (hc : (L ⊓ M) ⊓ N = ⊥) :
    Disjoint (L ⊓ M) (L ⊓ N) ∧ Disjoint (L ⊓ M) (M ⊓ N) ∧ Disjoint (L ⊓ N) (M ⊓ N) := by
  refine ⟨disjoint_iff.mpr (le_antisymm ?_ bot_le),disjoint_iff.mpr (le_antisymm ?_ bot_le),
    disjoint_iff.mpr (le_antisymm ?_ bot_le)⟩
  · intro x hx
    exact hc.le ⟨hx.1,hx.2.2⟩
  · intro x hx
    exact hc.le ⟨hx.1,hx.2.2⟩
  · intro x hx
    exact hc.le ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩

private instance certificate_instance_0072 : OAI.SidorenkoCounterexample.ProofCertificate_0072 := by
  constructor
  intros
  apply @certificate_proof_0072 <;> assumption

theorem certificate_proof_0073 (r p₀ p₁ p₂ : ℕ) :
    Function.Injective (subspaceProfile_to_config (K := K) (V := V) (r := r) (p₀ := p₀) (p₁ := p₁) (p₂ := p₂)) := by
  intro R S h
  let f : (Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P) →
      DimSubspace K V r × DimSubspace K V r × DimSubspace K V r := fun p => (p.2.1.val,p.2.2.1.val,p.2.2.2.val)
  exact Subtype.ext (congrArg f h)

private instance certificate_instance_0073 : OAI.SidorenkoCounterexample.ProofCertificate_0073 := by
  constructor
  intros
  apply @certificate_proof_0073 <;> assumption

variable [FiniteDimensional K V]
theorem certificate_proof_0074 (U W : Submodule K V) (h : Disjoint U W) :
    finrank K ↥(U ⊔ W) = finrank K U + finrank K W := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [h.eq_bot,finrank_bot,add_zero] at hh
  exact hh

private instance certificate_instance_0074 : OAI.SidorenkoCounterexample.ProofCertificate_0074 := by
  constructor
  intros
  apply @certificate_proof_0074 <;> assumption

variable [Fintype K]
theorem certificate_proof_0075 (p₀ p₁ p₂ : ℕ)
    (h₀ : p₀ ≤ finrank K V) (h₁ : p₁ ≤ finrank K V) (h₂ : p₂ ≤ finrank K V) :
    (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂)) := by
  let : Finite V := Module.finite_of_finite K
  have hc : Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) ≤
      Nat.card (DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hh : (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      (Nat.card (DimSubspace K V p₀) : ℝ) * Nat.card (DimSubspace K V p₁) * Nat.card (DimSubspace K V p₂) := by
    rw [Nat.card_prod, Nat.card_prod] at hc
    exact_mod_cast (hc.trans_eq (Nat.mul_assoc _ _ _).symm)
  calc
    _ ≤ _ := hh
    _ ≤ (2^p₀*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀))) *
      (2^p₁*(Fintype.card K : ℝ)^(p₁*(finrank K V-p₁))) *
      (2^p₂*(Fintype.card K : ℝ)^(p₂*(finrank K V-p₂))) := by
      exact mul_le_mul (mul_le_mul (subspace_count_upper p₀ h₀) (subspace_count_upper p₁ h₁)
        (by positivity) (by positivity)) (subspace_count_upper p₂ h₂) (by positivity) (by positivity)
    _ = _ := by simp only [pow_add]; ring

private instance certificate_instance_0075 : OAI.SidorenkoCounterexample.ProofCertificate_0075 := by
  constructor
  intros
  apply @certificate_proof_0075 <;> assumption

theorem certificate_proof_0076 {p₀ p₁ p₂ : ℕ} (r : ℕ)
    (P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleCompletion r P) : ℝ) ≤
      2^(3*r)*(Fintype.card K : ℝ)^((r-(p₀+p₁))*(finrank K V-r)+
        (r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)) := by
  let : Finite V := Module.finite_of_finite K
  have d₀ : finrank K ↥(P.val.1.val ⊔ P.val.2.1.val) = p₀+p₁ := by
    rw [disjoint_sup_finrank _ _ P.property.1,P.val.1.property,P.val.2.1.property]
  have d₁ : finrank K ↥(P.val.1.val ⊔ P.val.2.2.val) = p₀+p₂ := by
    rw [disjoint_sup_finrank _ _ P.property.2.1,P.val.1.property,P.val.2.2.property]
  have d₂ : finrank K ↥(P.val.2.1.val ⊔ P.val.2.2.val) = p₁+p₂ := by
    rw [disjoint_sup_finrank _ _ P.property.2.2,P.val.2.1.property,P.val.2.2.property]
  have a₀ := (containingSubspace_card_bounds (P.val.1.val ⊔ P.val.2.1.val) r (by omega) hr).2
  have a₁ := (containingSubspace_card_bounds (P.val.1.val ⊔ P.val.2.2.val) r (by omega) hr).2
  have a₂ := (containingSubspace_card_bounds (P.val.2.1.val ⊔ P.val.2.2.val) r (by omega) hr).2
  rw [d₀] at a₀
  rw [d₁] at a₁
  rw [d₂] at a₂
  have h := mul_le_mul (mul_le_mul a₀ a₁ (by positivity) (by positivity)) a₂ (by positivity) (by positivity)
  simpa only [SubspaceTripleCompletion,Nat.card_prod,Nat.cast_mul,pow_add,pow_mul,show 3*r=r+r+r by omega,
    mul_assoc,mul_left_comm,mul_comm] using h

private instance certificate_instance_0076 : OAI.SidorenkoCounterexample.ProofCertificate_0076 := by
  constructor
  intros
  apply @certificate_proof_0076 <;> assumption

theorem certificate_proof_0077 (r p₀ p₁ p₂ : ℕ)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent (finrank K V) r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂)
  have hc : (Nat.card (SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      Nat.card (Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (subspaceProfile_to_config_injective (K := K) (V := V) r p₀ p₁ p₂)
  let e := (r-(p₀+p₁))*(finrank K V-r)+(r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)
  calc
    _ ≤ _ := hc
    _ = ∑ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, (Nat.card (SubspaceTripleCompletion r P) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, 2^(3*r)*(Fintype.card K : ℝ)^e :=
      Finset.sum_le_sum (fun P _ => subspaceTripleCompletion_card_upper r P hr h₀ h₁ h₂)
    _ = (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ)*(2^(3*r)*(Fintype.card K : ℝ)^e) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂))) *
      (2^(3*r)*(Fintype.card K : ℝ)^e) := mul_le_mul_of_nonneg_right
        (pairSubspaceConfig_card_upper p₀ p₁ p₂ (by omega) (by omega) (by omega)) (by positivity)
    _ = _ := by dsimp [e,subspaceTripleExponent]; simp only [pow_add]; ring

private instance certificate_instance_0077 : OAI.SidorenkoCounterexample.ProofCertificate_0077 := by
  constructor
  intros
  apply @certificate_proof_0077 <;> assumption

end TripleSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SpanCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
omit [FiniteDimensional K V] in
theorem certificate_proof_0078 (r p₀ p₁ p₂ n : ℕ) :
    Function.Injective (spanProfileInjection (K := K) (V := V) r p₀ p₁ p₂ n) := by
  intro R S h
  let recover : (Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) →
      Submodule K V × Submodule K V × Submodule K V := fun ZR =>
    (ZR.2.val.1.val.map ZR.1.val.subtype,ZR.2.val.2.1.val.map ZR.1.val.subtype,
      ZR.2.val.2.2.val.map ZR.1.val.subtype)
  have he (T : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
      recover (spanProfileInjection r p₀ p₁ p₂ n T) =
      (T.val.val.1.val,T.val.val.2.1.val,T.val.val.2.2.val) := by
    let Z := T.val.val.1.val ⊔ T.val.val.2.1.val ⊔ T.val.val.2.2.val
    change ((T.val.val.1.val.comap Z.subtype).map Z.subtype,
      (T.val.val.2.1.val.comap Z.subtype).map Z.subtype,
      (T.val.val.2.2.val.comap Z.subtype).map Z.subtype) = _
    rw [Submodule.map_comap_subtype,Submodule.map_comap_subtype,Submodule.map_comap_subtype]
    rw [inf_eq_right.mpr (le_trans le_sup_left le_sup_left),
      inf_eq_right.mpr (le_trans le_sup_right le_sup_left),inf_eq_right.mpr le_sup_right]
  have hh := congrArg recover h
  rw [he,he] at hh
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh))
    (Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) hh)) (Subtype.ext (congrArg (fun z => z.2.2) hh)))

private instance certificate_instance_0078 : OAI.SidorenkoCounterexample.ProofCertificate_0078 := by
  constructor
  intros
  apply @certificate_proof_0078 <;> assumption

variable [Fintype K]
theorem certificate_proof_0079 (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^
        (n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (DimSubspace K V n)
  have hc : (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      Nat.card (Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (spanProfileInjection_injective (K := K) (V := V) r p₀ p₁ p₂ n)
  calc
    _ ≤ _ := hc
    _ = ∑ Z : DimSubspace K V n, (Nat.card (SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Z : DimSubspace K V n, 2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂) := by
      apply Finset.sum_le_sum
      intro Z _
      simpa only [Z.property] using subspaceTripleProfile_card_upper (K := K) (V := Z.val) r p₀ p₁ p₂
        (by simpa only [Z.property] using hr) h₀ h₁ h₂
    _ = (Nat.card (DimSubspace K V n) : ℝ) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^n*(Fintype.card K : ℝ)^(n*(finrank K V-n))) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂)) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper n hn) (by positivity)
    _ = _ := by simp only [pow_add]; ring

private instance certificate_instance_0079 : OAI.SidorenkoCounterexample.ProofCertificate_0079 := by
  constructor
  intros
  apply @certificate_proof_0079 <;> assumption

end SpanCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedSubspaceExponent
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K]
theorem certificate_proof_0080 (d n r p₀ p₁ p₂ : ℕ)
    (hn : n ≤ d) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    ((n*(d-n)+subspaceTripleExponent n r p₀ p₁ p₂ : ℕ) : ℝ) - (3*r*(d-r) : ℕ) =
      -((d:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) - ((d:ℝ)-n)*(3*r-n-(p₀+p₁+p₂)) := by
  have hp₀ : p₀ ≤ n := (Nat.le_add_right p₀ p₁).trans (h₀.trans hr)
  have hp₁ : p₁ ≤ n := (Nat.le_add_left p₁ p₀).trans (h₀.trans hr)
  have hp₂ : p₂ ≤ n := (Nat.le_add_left p₂ p₀).trans (h₁.trans hr)
  simp only [subspaceTripleExponent,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_sub hn,Nat.cast_sub hr,Nat.cast_sub (hr.trans hn),
    Nat.cast_sub hp₀,Nat.cast_sub hp₁,Nat.cast_sub hp₂,Nat.cast_sub h₀,Nat.cast_sub h₁,Nat.cast_sub h₂]
  ring

private instance certificate_instance_0080 : OAI.SidorenkoCounterexample.ProofCertificate_0080 := by
  constructor
  intros
  apply @certificate_proof_0080 <;> assumption

theorem certificate_proof_0081 (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(
        -((finrank K V:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) -
          ((finrank K V:ℝ)-n)*(3*r-n-(p₀+p₁+p₂))) := by
  let : Finite V := Module.finite_of_finite K
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hcount := subspaceTripleSpanProfile_card_upper (K := K) (V := V) r p₀ p₁ p₂ n hn hr h₀ h₁ h₂
  have hden : q^(3*r*(finrank K V-r)) ≤ (Nat.card (DimSubspace K V r) : ℝ)^3 := by
    have hu := subspace_count_lower (K := K) (V := V) r (hr.trans hn)
    have hh := pow_le_pow_left₀ (pow_nonneg hq.le _) hu 3
    simpa only [←pow_mul,Nat.mul_comm 3 r,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh
  have hp : 0 < (Nat.card (DimSubspace K V r) : ℝ)^3 := lt_of_lt_of_le (pow_pos hq _) hden
  have hdiv : (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
        (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      (2^(n+p₀+p₁+p₂+3*r)*q^(n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂)) /
        q^(3*r*(finrank K V-r)) := by
    exact div_le_div₀ (by positivity) hcount (pow_pos hq _) hden
  refine hdiv.trans_eq ?_
  rw [mul_div_assoc,←Real.rpow_natCast q (n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂),
    ←Real.rpow_natCast q (3*r*(finrank K V-r)),←Real.rpow_sub hq,
    subspace_span_cost_identity (finrank K V) n r p₀ p₁ p₂ hn hr h₀ h₁ h₂]

private instance certificate_instance_0081 : OAI.SidorenkoCounterexample.ProofCertificate_0081 := by
  constructor
  intros
  apply @certificate_proof_0081 <;> assumption

end PlantedSubspaceExponent
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualPlantedBases
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0082 (R : Submodule K (Module.Dual K V)) :
    finrank K R.dualCoannihilator + finrank K R = finrank K V := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq R.dualCoannihilator
  rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at h

private instance certificate_instance_0082 : OAI.SidorenkoCounterexample.ProofCertificate_0082 := by
  constructor
  intros
  apply @certificate_proof_0082 <;> assumption

theorem certificate_proof_0083 (R₀ R₁ R₂ : Submodule K (Module.Dual K V)) :
    finrank K ↥((R₀.dualCoannihilator ⊓ R₁.dualCoannihilator) ⊓ R₂.dualCoannihilator) =
      finrank K V - finrank K ↥((R₀ ⊔ R₁) ⊔ R₂) := by
  rw [←Submodule.dualCoannihilator_sup_eq,←Submodule.dualCoannihilator_sup_eq]
  have h := coannihilator_finrank ((R₀ ⊔ R₁) ⊔ R₂)
  omega

private instance certificate_instance_0083 : OAI.SidorenkoCounterexample.ProofCertificate_0083 := by
  constructor
  intros
  apply @certificate_proof_0083 <;> assumption

theorem certificate_proof_0084 (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) :
    finrank K ↥((dualGraph R B).val ⊓ verticalSpace (K := K) (V := V)) = finrank K R := by
  change finrank K ↥(formGraph R.dualCoannihilator B.val ⊓ verticalSpace (K := K) (V := V)) = _
  rw [graph_vertical_intersection_finrank]
  have h := coannihilator_finrank R
  omega

private instance certificate_instance_0084 : OAI.SidorenkoCounterexample.ProofCertificate_0084 := by
  constructor
  intros
  apply @certificate_proof_0084 <;> assumption

theorem certificate_proof_0085 (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) (f : Module.Dual K V) :
    ((0,f) : V × Module.Dual K V) ∈ (dualGraph R B).val ↔ f ∈ R := by
  change (∃ u : R.dualCoannihilator, u.val = 0 ∧ _ = B.val u) ↔ _
  constructor
  · rintro ⟨u,hu,hf⟩
    have hu0 : u = 0 := Subtype.ext hu
    have hf0 : f ∈ R.dualCoannihilator.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator (W := R.dualCoannihilator) f).mpr
      intro x hx
      have h := congrArg (fun l : Module.Dual K R.dualCoannihilator => l ⟨x,hx⟩) hf
      simpa [hu0] using h
    simpa only [Subspace.dualCoannihilator_dualAnnihilator_eq] using hf0
  · intro hf
    refine ⟨0,rfl,?_⟩
    ext x
    change f x.val = B.val 0 x
    rw [map_zero,LinearMap.zero_apply]
    have hx := (Submodule.mem_dualCoannihilator (Φ := R) x.val).mp x.property
    exact hx f hf

private instance certificate_instance_0085 : OAI.SidorenkoCounterexample.ProofCertificate_0085 := by
  constructor
  intros
  apply @certificate_proof_0085 <;> assumption

theorem certificate_proof_0086 (R₀ R₁ R₂ : Submodule K (Module.Dual K V))
    (F : OriginalForms R₀.dualCoannihilator R₁.dualCoannihilator R₂.dualCoannihilator)
    (h : ((dualGraph R₀ F.1).val ⊓ (dualGraph R₁ F.2.1).val) ⊓ (dualGraph R₂ F.2.2).val = ⊥) :
    (R₀ ⊓ R₁) ⊓ R₂ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have hm : ((0,f) : V × Module.Dual K V) ∈
      ((dualGraph R₀ F.1).val ⊓ (dualGraph R₁ F.2.1).val) ⊓ (dualGraph R₂ F.2.2).val :=
    ⟨⟨(dualGraph_vertical_subspace R₀ F.1 f).mpr hf.1.1,
       (dualGraph_vertical_subspace R₁ F.2.1 f).mpr hf.1.2⟩,
       (dualGraph_vertical_subspace R₂ F.2.2 f).mpr hf.2⟩
  have hz := h.le hm
  exact congrArg Prod.snd hz

private instance certificate_instance_0086 : OAI.SidorenkoCounterexample.ProofCertificate_0086 := by
  constructor
  intros
  apply @certificate_proof_0086 <;> assumption

end DualPlantedBases
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAll
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
theorem certificate_proof_0087 (t : ℕ) :
    (Nat.card {B : SymForm K V // t ≤ finrank K B.val.ker} : ℝ) / Nat.card (SymForm K V) ≤
      2^t / (Fintype.card K : ℝ)^((t+1).choose 2) := by
  by_cases ht : t ≤ finrank K V
  · exact symmetric_nullity_probability_bound t ht
  · have : IsEmpty {B : SymForm K V // t ≤ finrank K B.val.ker} :=
      ⟨fun B => ht (B.property.trans (Submodule.finrank_le B.val.val.ker))⟩
    rw [Nat.card_of_isEmpty,Nat.cast_zero,zero_div]
    positivity

private instance certificate_instance_0087 : OAI.SidorenkoCounterexample.ProofCertificate_0087 := by
  constructor
  intros
  apply @certificate_proof_0087 <;> assumption

end NullityAll
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAllLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
theorem certificate_proof_0088
    (t₀ t₁ t₂ : ℕ) :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have hc := linear_constraint_probability_bound
    (originalCyclicDifference A₀ A₁ A₂) (differenceConstraint A₀ A₁ A₂)
    (differenceConstraint_surjective A₀ A₁ A₂) (originalCyclicDifference_range A₀ A₁ A₂)
    (fun D => t₀ ≤ finrank K D.1.val.ker ∧ t₁ ≤ finrank K D.2.1.val.ker ∧
      t₂ ≤ finrank K D.2.2.val.ker)
  have hp := triple_predicate_probability
    (fun B : SymForm K ↥(A₁ ⊓ A₂) => t₀ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₂ ⊓ A₀) => t₁ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₀ ⊓ A₁) => t₂ ≤ finrank K B.val.ker)
  rw [mul_div_assoc, hp, symForm_card, Nat.cast_pow] at hc
  refine hc.trans ?_
  have hb₀ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₁ ⊓ A₂)) t₀
  have hb₁ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₂ ⊓ A₀)) t₁
  have hb₂ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₀ ⊓ A₁)) t₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (mul_le_mul hb₀ hb₁ (by positivity) (by positivity)) hb₂
    (by positivity) (by positivity)

private instance certificate_instance_0088 : OAI.SidorenkoCounterexample.ProofCertificate_0088 := by
  constructor
  intros
  apply @certificate_proof_0088 <;> assumption

theorem certificate_proof_0089 (t₀ t₁ t₂ : ℕ)
 :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have he (F : OriginalForms A₀ A₁ A₂) :
      (finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)) ↔
      (t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker) := by
    change (_ ≤ finrank K ↥(formGraph A₁ F.2.1.val ⊓ formGraph A₂ F.2.2.val) ∧
      _ ≤ finrank K ↥(formGraph A₂ F.2.2.val ⊓ formGraph A₀ F.1.val) ∧
      _ ≤ finrank K ↥(formGraph A₀ F.1.val ⊓ formGraph A₁ F.2.1.val)) ↔ _
    rw [graph_pair_intersection_finrank,graph_pair_intersection_finrank,graph_pair_intersection_finrank]
    simp only [Nat.add_le_add_iff_left]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact planted_nullity_probability_bound_all A₀ A₁ A₂ t₀ t₁ t₂

private instance certificate_instance_0089 : OAI.SidorenkoCounterexample.ProofCertificate_0089 := by
  constructor
  intros
  apply @certificate_proof_0089 <;> assumption

end NullityAllLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualProfileLift
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {r p₀ p₁ p₂ n : ℕ}
theorem certificate_proof_0090 [Fintype K] [Finite V]
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    Nat.card (DualProfileForms R) = (Fintype.card K)^(3*((finrank K V-r+1).choose 2)) := by
  have hdim (S : DimSubspace K (Module.Dual K V) r) : finrank K S.val.dualCoannihilator = finrank K V-r := by
    have h := coannihilator_finrank S.val
    rw [S.property] at h
    omega
  simp only [DualProfileForms,OriginalForms,Nat.card_prod,symForm_card,hdim,←pow_add]
  congr 1
  omega

private instance certificate_instance_0090 : OAI.SidorenkoCounterexample.ProofCertificate_0090 := by
  constructor
  intros
  apply @certificate_proof_0090 <;> assumption

theorem certificate_proof_0091 [Fintype K] [Finite V]
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :
    (Nat.card (DualLiftEvent R t₀ t₁ t₂) : ℝ) / Nat.card (DualProfileForms R) ≤
      2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
        (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2) := by
  let A₀ := R.val.val.1.val.dualCoannihilator
  let A₁ := R.val.val.2.1.val.dualCoannihilator
  let A₂ := R.val.val.2.2.val.dualCoannihilator
  have h₀ : finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) = p₂ := by
    dsimp only [A₁,A₂]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact R.val.property.2.2.2
  have h₁ : finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) = p₁ := by
    dsimp only [A₂,A₀]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq,inf_comm]
    exact R.val.property.2.2.1
  have h₂ : finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) = p₀ := by
    dsimp only [A₀,A₁]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact R.val.property.2.1
  have hv : finrank K (CommonSpace A₀ A₁ A₂) = finrank K V-n := by
    exact (coannihilator_common_finrank _ _ _).trans (by rw [R.property])
  have hb := lift_pair_profile_probability_bound_all A₀ A₁ A₂ t₂ t₁ t₀
  rw [h₀,h₁,h₂,hv] at hb
  refine hb.trans_eq ?_
  simp only [pow_add]
  ring

private instance certificate_instance_0091 : OAI.SidorenkoCounterexample.ProofCertificate_0091 := by
  constructor
  intros
  apply @certificate_proof_0091 <;> assumption

end DualProfileLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileConstraints
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0092 {r p₀ p₁ p₂ n : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
    n ≤ finrank K V ∧ r ≤ n ∧ p₀+p₁ ≤ r ∧ p₀+p₂ ≤ r ∧ p₁+p₂ ≤ r ∧
      n+(p₀+p₁+p₂) ≤ 3*r := by
  let A := R.val.val.1.val
  let B := R.val.val.2.1.val
  let C := R.val.val.2.2.val
  have hdis := triple_pairwise_disjoint A B C R.val.property.1
  have hdA : finrank K A = r := R.val.val.1.property
  have hdB : finrank K B = r := R.val.val.2.1.property
  have hdC : finrank K C = r := R.val.val.2.2.property
  have hp₀ : finrank K ↥(A ⊓ B) = p₀ := R.val.property.2.1
  have hp₁ : finrank K ↥(A ⊓ C) = p₁ := R.val.property.2.2.1
  have hp₂ : finrank K ↥(B ⊓ C) = p₂ := R.val.property.2.2.2
  have hn : finrank K ↥((A ⊔ B) ⊔ C) = n := R.property
  have ha : p₀+p₁ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ B) ⊔ (A ⊓ C) ≤ A from sup_le inf_le_left inf_le_left)
    rwa [disjoint_sup_finrank _ _ hdis.1,hp₀,hp₁,hdA] at h
  have hb : p₀+p₂ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ B) ⊔ (B ⊓ C) ≤ B from sup_le inf_le_right inf_le_left)
    rwa [disjoint_sup_finrank _ _ hdis.2.1,hp₀,hp₂,hdB] at h
  have hc : p₁+p₂ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ C) ⊔ (B ⊓ C) ≤ C from sup_le inf_le_right inf_le_right)
    rwa [disjoint_sup_finrank _ _ hdis.2.2,hp₁,hp₂,hdC] at h
  refine ⟨hn ▸ Submodule.finrank_le _,?_,ha,hb,hc,?_⟩
  · have h := Submodule.finrank_mono (show A ≤ (A ⊔ B) ⊔ C from le_trans le_sup_left le_sup_left)
    rwa [hdA,hn] at h
  · have h₁ := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) C
    have h₃ := Submodule.finrank_mono (show (A ⊓ C) ⊔ (B ⊓ C) ≤ (A ⊔ B) ⊓ C from
      sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl))
    rw [disjoint_sup_finrank _ _ hdis.2.2,hp₁,hp₂] at h₃
    rw [hdA,hdB,hp₀] at h₁
    rw [hn,hdC] at h₂
    omega

private instance certificate_instance_0092 : OAI.SidorenkoCounterexample.ProofCertificate_0092 := by
  constructor
  intros
  apply @certificate_proof_0092 <;> assumption

end ProfileConstraints
section DualLiftSum
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype K] [Finite V]
theorem certificate_proof_0093 (r : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card {L : Lagrangian (K := K) (V := V) //
      finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r} : ℝ)^3 =
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3 *
        (Fintype.card K : ℝ)^(3*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 3]

private instance certificate_instance_0093 : OAI.SidorenkoCounterexample.ProofCertificate_0093 := by
  constructor
  intros
  apply @certificate_proof_0093 <;> assumption

theorem certificate_proof_0094 (r p₀ p₁ p₂ n t₀ t₁ t₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n,
      DualLiftEvent R t₀ t₁ t₂) : ℝ) /
      (Nat.card {L : Lagrangian (K := K) (V := V) //
        finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r} : ℝ)^3 ≤
    ((Nat.card (SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3) *
    (2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
      (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let RType := SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
  let : Fintype RType := Fintype.ofFinite _
  let q : ℝ := Fintype.card K
  let f := 3*((finrank K V-r+1).choose 2)
  let b : ℝ := 2^(t₀+t₁+t₂)*q^((finrank K V-n+1).choose 2)/
    q^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hF : 0 < q^f := pow_pos hq _
  have hb (R : RType) : (Nat.card (DualLiftEvent R t₀ t₁ t₂) : ℝ) ≤ b*q^f := by
    have h := dual_lift_probability_bound R t₀ t₁ t₂
    rw [dualProfileForms_card,Nat.cast_pow] at h
    exact (div_le_iff₀ hF).mp h
  have hc : (Nat.card (Σ R : RType, DualLiftEvent R t₀ t₁ t₂) : ℝ) ≤
      (Nat.card RType : ℝ)*b*q^f := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _R : RType, b*q^f := Finset.sum_le_sum (fun R _ => hb R)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Nat.card_eq_fintype_card]; ring
  rw [center_stratum_cube r hr]
  refine (div_le_div_of_nonneg_right hc (by positivity)).trans_eq ?_
  change (Nat.card RType : ℝ)*b*q^f / ((Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3*q^f) = _
  rw [mul_div_mul_right _ _ hF.ne']
  ring

private instance certificate_instance_0094 : OAI.SidorenkoCounterexample.ProofCertificate_0094 := by
  constructor
  intros
  apply @certificate_proof_0094 <;> assumption

end DualLiftSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0095 (r : ℕ) (hr : r ≤ finrank K V)
    (R : DimSubspace K (Module.Dual K V) r) (F : SymForm K R.val.dualCoannihilator) :
    (dualPairStratumEquiv r hr ⟨R,F⟩).val = dualGraph R.val F := rfl

private instance certificate_instance_0095 : OAI.SidorenkoCounterexample.ProofCertificate_0095 := by
  constructor
  intros
  apply @certificate_proof_0095 <;> assumption

theorem certificate_proof_0096 (r : ℕ) (hr : r ≤ finrank K V)
    (RF : Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) :
    ((dualTripleStratumEquiv r hr RF).1.val,(dualTripleStratumEquiv r hr RF).2.1.val,
      (dualTripleStratumEquiv r hr RF).2.2.val) = dualBaseTripleGraph RF.1 RF.2 := rfl

private instance certificate_instance_0096 : OAI.SidorenkoCounterexample.ProofCertificate_0096 := by
  constructor
  intros
  apply @certificate_proof_0096 <;> assumption

theorem certificate_proof_0097 (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥(R ⊓ S) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  change _ ≤ finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val)
  rw [graph_pair_intersection_finrank,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.le_add_right _ _

private instance certificate_instance_0097 : OAI.SidorenkoCounterexample.ProofCertificate_0097 := by
  constructor
  intros
  apply @certificate_proof_0097 <;> assumption

end CanonicalCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ExtraFeasibility
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem certificate_proof_0098 (R S : Submodule K (Module.Dual K V)) :
    finrank K ↥(R.dualCoannihilator ⊓ S.dualCoannihilator) + finrank K R + finrank K S =
      finrank K V + finrank K ↥(R ⊓ S) := by
  rw [←Submodule.dualCoannihilator_sup_eq]
  have h := coannihilator_finrank (R ⊔ S)
  have hg := Submodule.finrank_sup_add_finrank_inf_eq R S
  omega

private instance certificate_instance_0098 : OAI.SidorenkoCounterexample.ProofCertificate_0098 := by
  constructor
  intros
  apply @certificate_proof_0098 <;> assumption

theorem certificate_proof_0099 (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) ≤
      finrank K ↥(R ⊓ S)+finrank K ↥(R.dualCoannihilator ⊓ S.dualCoannihilator) := by
  change finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val) ≤ _
  rw [graph_pair_intersection_finrank,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _

private instance certificate_instance_0099 : OAI.SidorenkoCounterexample.ProofCertificate_0099 := by
  constructor
  intros
  apply @certificate_proof_0099 <;> assumption

end ExtraFeasibility
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalParameterCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end CanonicalParameterCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CanonicalNumericalBound
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]
end CanonicalNumericalBound
end SidorenkoCounterexample
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0069 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0070 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0071 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0072 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0073 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0074 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0075 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0076 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0077 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0078 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0079 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0080 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0081 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0082 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0083 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0084 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0085 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0086 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0087 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0088 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0089 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0090 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0091 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0092 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0093 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0094 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0095 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0096 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0097 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0098 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0099 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

