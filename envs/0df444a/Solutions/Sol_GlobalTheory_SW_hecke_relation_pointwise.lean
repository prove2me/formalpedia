-- Prove2me | solution 1 for GlobalTheory.SW.hecke_relation_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:01.643484+00:00
-- url     : https://prove2.me/submissions/ecfbef6f-5a55-491d-96df-4e3ceed1cb7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_smul_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_exists_not_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_exists_lines
import Theorems.Thm_GlobalTheory_SW_HeckeId_exists_reps
import Theorems.Thm_GlobalTheory_SW_HeckeId_finrank_of_agree
import Theorems.Thm_GlobalTheory_SW_HeckeId_gidx_of_le
import Theorems.Thm_GlobalTheory_SW_HeckeId_exists_pole
import Theorems.Thm_GlobalTheory_SW_HeckeId_pole_smul_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_ccT_sym
import Theorems.Thm_GlobalTheory_SW_HeckeId_chiH_sym
import Theorems.Thm_GlobalTheory_SW_HeckeId_count_pole
import Theorems.Thm_GlobalTheory_SW_HeckeId_count_int
import Theorems.Thm_GlobalTheory_SW_HeckeId_pairChar_spec
import Theorems.Thm_GlobalTheory_SW_HeckeId_finsum_ite
import Theorems.Thm_P2M_GlobalTheory_SW_HeckeId_sum_ite__fd2c2018495e
import Theorems.Thm_P2M_GlobalTheory_SW_HeckeId_exists_mult__e6066571aebc
import Theorems.Thm_GlobalTheory_SW_HeckeId_twist_ite
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_Hyper_count
import Theorems.Thm_GlobalTheory_SW_Hyper_exists_fun
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_symm
import Theorems.Thm_GlobalTheory_SW_Nbr_agree_trans
import Theorems.Thm_GlobalTheory_SW_Nbr_conj_le
import Theorems.Thm_GlobalTheory_SW_Nbr_exists_not_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_fg_of_agree
import Theorems.Thm_GlobalTheory_SW_Nbr_finrank_eq
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_index_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_GlobalTheory_SW_Nbr_nb_count
import Theorems.Thm_GlobalTheory_SW_Nbr_ne_bot_of_norm
import Theorems.Thm_GlobalTheory_SW_Nbr_proj
import Theorems.Thm_GlobalTheory_SW_Nbr_relIndex_eq
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_GlobalTheory_SW_TwistAdm_col_eq
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_TwistAdm_single_mem_std
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory.SW.HeckeId GlobalTheory.SW.Nbr
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (M R q : ℕ) (P : Ideal (𝓞 E)) (φ : Fam E n N) (𝔛 : Lt E N), admitted M R φ → 𝔛.FG → Agree (R * M) 𝔛 (stdL E N) → GoodPrime (R * M) q P → ∃ (A : ℕ) (XA XB : Fin A → Lt E N) (β : Fin A → Fin (q ^ N) → Matrix (Fin N) (Fin N) E), A * (q - 1) = q ^ N - 1 ∧ (∀ i, (XA i).FG ∧ Agree (R * M) (XA i) (stdL E N) ∧ gidx (XA i) = q * gidx 𝔛 ∧ (XB i).FG ∧ Agree (R * M) (XB i) (stdL E N) ∧ q * gidx (XB i) = gidx 𝔛 ∧ ∀ j, ccT (β i j) = β i j) ∧ ∀ Λ ∈ Vset E n M, ∀ x, ((q : ℂ) - 1) * ((q : ℂ) ^ n * ∑ i, twist R (XA i) φ Λ x + ∑ i, ∑ j, chiH Ψ (β i j) x * twist R (XB i) φ Λ x) = ((q : ℂ) - 1) * (q : ℂ) ^ N * (∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x) + ((q : ℂ) ^ (2 * N) - (q : ℂ) ^ n) * twist R 𝔛 φ Λ x := by
  intro E _ _ _ Ψ hΨ n N M R q P φ 𝔛 hφ hfg hA hP'
  have hP : GoodPrime M q P := ⟨hP'.1, Nat.Coprime.coprime_mul_left_right hP'.2.1, hP'.2.2⟩
  have hQ := good_conj hP
  have hq := hP.1
  have mP := max_of_norm hq hP.2.2.1
  have mQ := max_of_norm hq hQ.2.2.1
  have cP : Nat.card (𝓞 E ⧸ P) = q := hP.2.2.1
  have cQ : Nat.card (𝓞 E ⧸ conjI P) = q := hQ.2.2.1
  have : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (cP ▸ hq.ne_zero)
  have : Finite (𝓞 E ⧸ conjI P) := Nat.finite_of_card_ne_zero (cQ ▸ hq.ne_zero)
  have qP : ((q : ℕ) : 𝓞 E) ∈ P := hP.2.2.1 ▸ Ideal.absNorm_mem P
  have qQ : ((q : ℕ) : 𝓞 E) ∈ conjI P := hQ.2.2.1 ▸ Ideal.absNorm_mem _
  have := proj hfg
  have : Module.Finite (𝓞 E) 𝔛 := Module.Finite.iff_fg.mpr hfg
  have hrk := finrank_of_agree hA
  obtain ⟨A, e, hA1, he, hcount⟩ := exists_lines (M := 𝔛) P
  rw [cP, hrk] at hA1 hcount
  obtain ⟨-, hH⟩ := Hyper.count (M := 𝔛) (conjI P)
  rw [cQ, hrk, ← hA1] at hH
  have hH' : Nat.card (Hyp (conjI P) 𝔛) = A :=
    Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq.one_lt) hH
  have : Finite (Hyp (conjI P) 𝔛) := (Hyper.count (M := 𝔛) (conjI P)).1
  let ε := Finite.equivFinOfCardEq hH'
  obtain ⟨B, hB, hB1, hB2⟩ : ∃ B : Fin A → Submodule (𝓞 E) 𝔛, (∀ i, B i ∈ Hyp (conjI P) 𝔛) ∧
      Function.Injective B ∧ ∀ K ∈ Hyp (conjI P) 𝔛, ∃ i, B i = K :=
    ⟨fun i => (ε.symm i).1, fun i => (ε.symm i).2, Subtype.val_injective.comp ε.symm.injective,
      fun K hK => ⟨ε ⟨K, hK⟩, by simp⟩⟩
  choose η hη using fun i => Hyp.exists_not_mem (hB i)
  obtain ⟨ξ, hξ⟩ := exists_reps (M := 𝔛) P (B := q ^ N) (by rw [cP, hrk])
  obtain ⟨t, ht, d, hd, r, hr, edr⟩ := exists_pole P (ne_bot_of_norm hq hP.2.2.1)
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hP.2.2.2.1
  obtain ⟨s, hs, hs1⟩ := exists_mult' hφ.pos.2 hP'.2.1 hA
  let XA : Fin A → Lt E N := fun i => 𝔛 ⊔ Submodule.span (𝓞 E) {t • (e i : Fin N → E)}
  let XB : Fin A → Lt E N := fun i => (B i).map 𝔛.subtype
  have mA : ∀ i v, v ∈ XA i ↔ ∃ y ∈ 𝔛, ∃ c : 𝓞 E, y + c • t • (e i : Fin N → E) = v := by
    intro i v
    simp only [XA, Submodule.mem_sup, Submodule.mem_span_singleton]
    exact ⟨fun ⟨y, hy, _, ⟨c, rfl⟩, h⟩ => ⟨y, hy, c, h⟩, fun ⟨y, hy, c, h⟩ => ⟨y, hy, _, ⟨c, rfl⟩, h⟩⟩
  have pA : ∀ i, ∀ c ∈ P, c • t • (e i : Fin N → E) ∈ 𝔛 := fun i c hc => by
    rw [osmul, smul_smul]
    exact 𝔛.smul_mem (⟨_, ht c hc⟩ : 𝓞 E) (e i).2
  have qB : ∀ i, ∀ v ∈ 𝔛, (q : E) • v ∈ XB i := fun i v hv =>
    ⟨_, Hyp.smul_mem (hB i) qQ ⟨v, hv⟩, rfl⟩
  have aA : ∀ i, Agree (R * M) 𝔛 (XA i) := fun i =>
    ⟨q, hq.pos, hP'.2.1, fun v hv => Submodule.mem_sup_left (Base.nat_smul_mem _ _ hv), fun v hv => by
      obtain ⟨y, hy, c, rfl⟩ := (mA i v).1 hv
      rw [smul_add, smul_comm (q : E) c]
      exact add_mem (Base.nat_smul_mem _ _ hy) (𝔛.smul_mem c (pA i _ qP))⟩
  have aB : ∀ i, Agree (R * M) 𝔛 (XB i) := fun i =>
    ⟨q, hq.pos, hP'.2.1, qB i, fun v hv => Base.nat_smul_mem _ _ (𝔛.map_subtype_le _ hv)⟩
  have aA' := fun i => agree_trans (agree_symm (aA i)) hA
  have aB' := fun i => agree_trans (agree_symm (aB i)) hA
  refine ⟨A, XA, XB, fun i j => sym ((R : E) • (η i : Fin N → E)) ((R : E) • ((b • ξ j : 𝔛) : Fin N → E)),
    hA1, fun i => ⟨fg_of_agree hfg (aA i), aA' i, gidx_of_le hA le_sup_left ?_,
      fg_of_agree hfg (aB i), aB' i, (gidx_of_le (aB' i) (𝔛.map_subtype_le _) ?_).symm,
      fun j => ccT_sym _ _⟩, fun Λ hΛ x => ?_⟩
  · rw [relIndex_eq]
    refine ((index_iff hq hP.2.2.1 _).2 (Hyper.exists_fun P _
      ⟨t • (e i : Fin N → E), Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩
      (fun h => he i ((pole_smul_mem ht hd hr edr 𝔛 (e i)).1 h)) (pA i) fun v => ?_)).2
    obtain ⟨y, hy, c, h⟩ := (mA i v).1 v.2
    refine ⟨c, ?_⟩
    change (v : Fin N → E) - c • t • (e i : Fin N → E) ∈ 𝔛
    rwa [← h, add_sub_cancel_right]
  · rw [relIndex_eq, Submodule.comap_map_eq_of_injective 𝔛.injective_subtype]
    exact ((index_iff hq hQ.2.2.1 _).2 (hB i)).2
  have hS : SD Λ := hΛ.2.1
  obtain ⟨u, hu⟩ : ∃ u : 𝔛 →ₗ[𝓞 E] (Fin n → E), ∀ v, u v = (R : E) • (x *ᵥ v) :=
    ⟨(((R : E) • x).mulVecLin.restrictScalars (𝓞 E)) ∘ₗ 𝔛.subtype, fun v =>
      Matrix.smul_mulVec (R : E) x (v : Fin N → E)⟩
  have cX : ∀ L : Lt E n, (∀ v ∈ 𝔛, (R : E) • (x *ᵥ v) ∈ L) ↔ ∀ v, u v ∈ L := fun L => by
    simp only [hu, Subtype.forall]
  have sX : ∀ v ∈ stdL E N, (s : E) • v ∈ 𝔛 := fun v hv => by
    obtain ⟨w, hw, h⟩ := hs1 v hv
    rw [h]; exact Base.nat_smul_mem _ _ hw
  set c := φ Λ ((s : E) • x) with hc
  have e1 : ∑ i, twist R (XA i) φ Λ x = ({i | (∀ v, u v ∈ Λ) ∧ t • u (e i) ∈ Λ}.ncard : ℂ) * c := by
    refine sum_ite' _ _ _ fun i => ?_
    rw [twist_ite hφ (aA' i) hΛ x hs fun v hv => Submodule.mem_sup_left (sX v hv)]
    refine if_congr ⟨fun h => ⟨(cX Λ).1 fun v hv => h v (Submodule.mem_sup_left hv), ?_⟩,
      fun h v hv => ?_⟩ rfl rfl
    · have := h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      rwa [Matrix.mulVec_smul, smul_comm, ← hu] at this
    · obtain ⟨y, hy, c, rfl⟩ := (mA i v).1 hv
      rw [Matrix.mulVec_add, smul_add, osmul, Matrix.mulVec_smul, Matrix.mulVec_smul,
        smul_comm (R : E) (c : E), smul_comm (R : E) t, ← hu]
      exact add_mem ((cX Λ).2 h.1 y hy) (Λ.smul_mem c h.2)
  have e2 : ∑ i, ∑ j, chiH Ψ (sym ((R : E) • (η i : Fin N → E))
      ((R : E) • ((b • ξ j : 𝔛) : Fin N → E))) x * twist R (XB i) φ Λ x =
      ({i | (∀ v ∈ B i, u v ∈ Λ) ∧ ∀ v, Int' (u (η i)) (u (b • v))}.ncard : ℂ) * (q ^ N * c) := by
    refine sum_ite' _ _ _ fun i => ?_
    rw [← Finset.sum_mul, twist_ite hφ (aB' i) hΛ x hs fun v hv => by
      obtain ⟨w, hw, h⟩ := hs1 v hv
      rw [h]; exact qB i w hw]
    have k : (∀ v ∈ XB i, (R : E) • (x *ᵥ v) ∈ Λ) ↔ ∀ v ∈ B i, u v ∈ Λ :=
      ⟨fun h v hv => hu v ▸ h _ ⟨v, hv, rfl⟩, fun h _ ⟨v, hv, e⟩ => e ▸ hu v ▸ h v hv⟩
    by_cases h : ∀ v ∈ B i, u v ∈ Λ
    · obtain ⟨k1, k2⟩ := pairChar_spec hP hS hb u (fun c hc v => h _ (Hyp.smul_mem (hB i) hc v)) (η i)
      have k3 : ∀ j, chiH Ψ (sym ((R : E) • (η i : Fin N → E))
          ((R : E) • ((b • ξ j : 𝔛) : Fin N → E))) x = pairChar u b (η i) (ξ j) := fun j => by
        rw [chiH_sym hΨ, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hu, ← hu]; rfl
      rw [if_pos (k.2 h), Finset.sum_congr rfl fun j _ => k3 j, hξ _ k1]
      by_cases h2 : ∀ v, Int' (u (η i)) (u (b • v))
      · rw [if_pos (k2.2 h2), if_pos ⟨h, h2⟩, Nat.cast_pow]
      · rw [if_neg (fun H => h2 (k2.1 H)), if_neg (fun H => h2 H.2), zero_mul]
    · rw [if_neg (fun H => h (k.1 H)), if_neg (fun H => h H.1), mul_zero]
  have e3 : ∑ᶠ Λ' ∈ Nb M P Λ, twist R 𝔛 φ Λ' x =
      ({Λ' ∈ Nb M P Λ | ∀ v, u v ∈ Λ'}.ncard : ℂ) * c := by
    refine finsum_ite (nb_count hP hΛ).1 _ _ _ fun Λ' h' => ?_
    rw [twist_ite hφ hA h'.1 x hs sX]
    refine if_ctx_congr (cX Λ') (fun h => (hφ.loc Λ hΛ Λ' h'.1
      (agree_of_le hP hP'.2.1 hS h'.1.2.1 h'.2.1) _ (fun k => ?_)
      (TwistAdm.cols_of_cond sX ((cX Λ').2 h))).symm) fun _ => rfl
    obtain ⟨w, hw, h1⟩ := hs1 _ (TwistAdm.single_mem_std k)
    rw [TwistAdm.col_eq, Matrix.smul_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h1,
      Matrix.mulVec_smul, smul_comm]
    exact smul_le_iff.1 (conj_le hS h'.1.2.1 h'.2.1) _ qQ _ ((cX Λ').2 h w hw)
  rw [e1, e2, e3, twist_ite hφ hA hΛ x hs sX]
  by_cases h : ∀ v, u v ∈ Λ
  · have := proj hΛ.1
    have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hΛ.1
    have k1 := hcount Λ (u.codRestrict Λ h)
    rw [finrank_eq hΛ, ← count_int hP hΛ u h] at k1
    have k2 : Nat.card {i // u.codRestrict Λ h (e i) ∈ (P • ⊤ : Submodule (𝓞 E) Λ)} =
        {i | (∀ v, u v ∈ Λ) ∧ t • u (e i) ∈ Λ}.ncard :=
      Nat.card_congr (Equiv.subtypeEquivRight fun i =>
        (pole_smul_mem ht hd hr edr Λ _).symm.trans (and_iff_right h).symm)
    have k3 : {i | (∀ v ∈ B i, u v ∈ Λ) ∧ ∀ v, Int' (u (η i)) (u (b • v))}.ncard = A := by
      rw [Set.eq_univ_of_forall (s := {i | (∀ v ∈ B i, u v ∈ Λ) ∧ _})
        fun i => ⟨fun v _ => h v, fun v => (hS _).1 (h _) _ (h _)⟩]
      simp [Set.ncard_univ]
    rw [k2] at k1
    rw [k3, if_pos ((cX Λ).2 h), ← hc]
    have k4 := congrArg (Nat.cast : ℕ → ℂ) k1
    have k5 := congrArg (Nat.cast : ℕ → ℂ) hA1
    push_cast [Nat.cast_sub hq.one_le, Nat.cast_sub (Nat.one_le_pow N q hq.pos)] at k4 k5
    linear_combination c * k4 + (q : ℂ) ^ N * c * k5
  · rw [count_pole hP hΛ ha hab u h B hB hB1 hB2 η hη, if_neg fun H => h ((cX Λ).1 H),
      Set.eq_empty_of_forall_notMem (s := {i | (∀ v, u v ∈ Λ) ∧ _}) fun i H => h H.1]
    simp only [Set.ncard_empty, Nat.cast_zero]
    ring
end GlobalTheory.SW
