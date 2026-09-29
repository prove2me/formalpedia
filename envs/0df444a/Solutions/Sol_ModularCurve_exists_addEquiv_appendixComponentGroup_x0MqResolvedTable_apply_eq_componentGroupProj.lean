-- Prove2me | solution 1 for ModularCurve.exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ecfe8712-9de1-5c6f-9b21-b2941cb59f5a

import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj

open ModularCurve MazurRapoportAppendix Finset

namespace NeronObjPathIso

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)

omit [DecidableEq ι] in
theorem sum_components (F : X0MqComponents e → ℤ) :
    ∑ j, F j = F (Sum.inl 0) + F (Sum.inl 1) + ∑ s : ι, ∑ k : Fin (e s - 1), F (Sum.inr ⟨s, k⟩) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  congr 1
  rw [Fintype.sum_sigma]

theorem sum_ite_val_succ_eq {n : ℕ} (k : Fin n) (g : Fin n → ℤ) :
    ∑ k' : Fin n, (if k'.val + 1 = k.val then g k' else 0) =
      if h : k.val = 0 then 0 else g ⟨k.val - 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun k' _ => by rw [if_neg]; omega
  · rw [Finset.sum_eq_single ⟨k.val - 1, by omega⟩]
    · rw [if_pos]; simp only; omega
    · intro k' _ hk'
      rw [if_neg]
      intro h'
      apply hk'
      ext; simp only; omega
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem sum_ite_val_eq_succ {n : ℕ} (k : Fin n) (g : Fin n → ℤ) :
    ∑ k' : Fin n, (if k.val + 1 = k'.val then g k' else 0) =
      if h : k.val + 1 < n then g ⟨k.val + 1, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k.val + 1, h⟩]
    · simp
    · intro k' _ hk'
      rw [if_neg]
      intro h'
      apply hk'
      ext; simp only; omega
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · exact Finset.sum_eq_zero fun k' _ => by rw [if_neg]; omega

def ofProfile (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) : X0MqComponents e → ℤ
  | Sum.inl i => if i = 0 then b₀ else b₁
  | Sum.inr p => g p.1 (p.2.val + 1)

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] theorem ofProfile_inl_zero (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) :
    ofProfile e b₀ b₁ g (Sum.inl 0) = b₀ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] theorem ofProfile_inl_one (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) :
    ofProfile e b₀ b₁ g (Sum.inl 1) = b₁ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] theorem ofProfile_inr (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) (s : ι) (k : Fin (e s - 1)) :
    ofProfile e b₀ b₁ g (Sum.inr ⟨s, k⟩) = g s (k.val + 1) := rfl

theorem rowSum_inr (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) (s : ι) (k : Fin (e s - 1)) :
    ∑ i, ofProfile e b₀ b₁ g i * (x0MqAdj e i (Sum.inr ⟨s, k⟩) : ℤ) =
      (if k.val = 0 then b₀ else g s k.val) +
        (if k.val + 1 < e s - 1 then g s (k.val + 1 + 1) else b₁) := by
  have hk := k.2
  rw [sum_components]
  simp only [ofProfile_inl_zero, ofProfile_inl_one, ofProfile_inr]
  have h0 : (x0MqAdj e (Sum.inl 0) (Sum.inr ⟨s, k⟩) : ℤ) = if k.val = 0 then 1 else 0 := by
    simp only [x0MqAdj, true_and, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, false_and, or_false]
    split_ifs <;> simp
  have h1 : (x0MqAdj e (Sum.inl 1) (Sum.inr ⟨s, k⟩) : ℤ) = if k.val = e s - 2 then 1 else 0 := by
    simp only [x0MqAdj, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, false_and, true_and, false_or]
    split_ifs <;> simp
  have h2 : ∑ s' : ι, ∑ k' : Fin (e s' - 1),
      g s' (k'.val + 1) * (x0MqAdj e (Sum.inr ⟨s', k'⟩) (Sum.inr ⟨s, k⟩) : ℤ) =
      ∑ k' : Fin (e s - 1), g s (k'.val + 1) *
        (if k'.val + 1 = k.val ∨ k.val + 1 = k'.val then 1 else 0 : ℤ) := by
    rw [Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun k' _ => ?_
      simp only [x0MqAdj, true_and]
      split_ifs <;> simp
    · intro s' _ hs'
      refine Finset.sum_eq_zero fun k' _ => ?_
      simp only [x0MqAdj]
      rw [if_neg (fun h => hs' h.1)]
      simp
    · intro h; exact absurd (Finset.mem_univ s) h
  rw [h0, h1, h2]
  have h3 : ∑ k' : Fin (e s - 1), g s (k'.val + 1) *
        (if k'.val + 1 = k.val ∨ k.val + 1 = k'.val then 1 else 0 : ℤ) =
      (∑ k' : Fin (e s - 1), if k'.val + 1 = k.val then g s (k'.val + 1) else 0) +
      ∑ k' : Fin (e s - 1), if k.val + 1 = k'.val then g s (k'.val + 1) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    by_cases ha : k'.val + 1 = k.val
    · rw [if_pos (Or.inl ha), if_pos ha, if_neg (by omega)]; ring
    · by_cases hb : k.val + 1 = k'.val
      · rw [if_pos (Or.inr hb), if_neg ha, if_pos hb]; ring
      · rw [if_neg (by tauto), if_neg ha, if_neg hb]; ring
  rw [h3, sum_ite_val_succ_eq, sum_ite_val_eq_succ]
  by_cases hk0 : k.val = 0
  · rw [if_pos hk0, dif_pos hk0, if_pos hk0]
    by_cases hk2 : k.val + 1 < e s - 1
    · have hne : ¬ k.val = e s - 2 := by omega
      rw [if_neg hne, dif_pos hk2, if_pos hk2]; ring
    · have heq : k.val = e s - 2 := by omega
      rw [if_pos heq, dif_neg hk2, if_neg hk2]; ring
  · have hsub : k.val - 1 + 1 = k.val := by omega
    rw [if_neg hk0, dif_neg hk0, if_neg hk0, hsub]
    by_cases hk2 : k.val + 1 < e s - 1
    · have hne : ¬ k.val = e s - 2 := by omega
      rw [if_neg hne, dif_pos hk2, if_pos hk2]; ring
    · have heq : k.val = e s - 2 := by omega
      rw [if_pos heq, dif_neg hk2, if_neg hk2]; ring

theorem rowSum_inl_zero (he : ∀ s, 0 < e s) (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) :
    ∑ i, ofProfile e b₀ b₁ g i * (x0MqAdj e i (Sum.inl 0) : ℤ) =
      ∑ s : ι, (if 1 < e s then g s 1 else b₁) := by
  rw [sum_components]
  simp only [ofProfile_inl_zero, ofProfile_inl_one, ofProfile_inr]
  have h00 : (x0MqAdj e (Sum.inl 0) (Sum.inl 0) : ℤ) = 0 := by simp [x0MqAdj]
  have h10 : (x0MqAdj e (Sum.inl 1) (Sum.inl 0) : ℤ) = ((univ.filter fun x => e x = 1).card : ℤ) := by
    simp [x0MqAdj]
  have h2 : ∀ (s' : ι) (k' : Fin (e s' - 1)),
      (x0MqAdj e (Sum.inr ⟨s', k'⟩) (Sum.inl 0) : ℤ) = if k'.val = 0 then 1 else 0 := by
    intro s' k'
    simp only [x0MqAdj, true_and, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, false_and, or_false]
    split_ifs <;> simp
  simp only [h00, h10, h2, mul_zero, zero_add, mul_ite, mul_one]
  have h3 : ∀ s' : ι, ∑ k' : Fin (e s' - 1), (if k'.val = 0 then g s' (k'.val + 1) else 0) =
      if 0 < e s' - 1 then g s' 1 else 0 := by
    intro s'
    split_ifs with hpos
    · rw [Finset.sum_eq_single ⟨0, hpos⟩]
      · simp
      · intro k' _ hk'
        rw [if_neg]
        intro h; apply hk'; ext; exact h
      · intro h; exact absurd (Finset.mem_univ _) h
    · exact Finset.sum_eq_zero fun k' _ => absurd k'.2 (by omega)
  simp only [h3]
  have h4 : ((univ.filter fun x => e x = 1).card : ℤ) = ∑ s : ι, if e s = 1 then (1 : ℤ) else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    simp
  rw [h4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := he s
  by_cases h1 : e s = 1
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]; ring
  · rw [if_neg h1, if_pos (by omega), if_pos (by omega)]; ring

theorem alpha_apply (c : X0MqComponents e → ℤ) (j : X0MqComponents e) :
    intersectionAlpha (x0MqResolvedTable e) c j =
      (∑ i, c i * (x0MqAdj e i j : ℤ)) - c j * ∑ i, (x0MqAdj e i j : ℤ) := by
  rw [intersectionAlpha_apply]
  have : ∀ i, c i * (x0MqResolvedTable e).inter i j =
      c i * (x0MqAdj e i j : ℤ) - if i = j then c j * ∑ j', (x0MqAdj e j j' : ℤ) else 0 := by
    intro i
    show c i * ((x0MqAdj e i j : ℤ) - if i = j then ∑ j', (x0MqAdj e i j' : ℤ) else 0) = _
    split_ifs with h
    · subst h; ring
    · ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [x0MqAdj_symm]

omit [Fintype ι] in

theorem ofProfile_one : ofProfile e 1 1 (fun _ _ => 1) = fun _ => 1 := by
  funext j
  rcases j with i | ⟨s, k⟩
  · fin_cases i <;> rfl
  · rfl

theorem degree_inr (s : ι) (k : Fin (e s - 1)) :
    ∑ i, (x0MqAdj e i (Sum.inr ⟨s, k⟩) : ℤ) = 2 := by
  have := rowSum_inr e 1 1 (fun _ _ => 1) s k
  rw [ofProfile_one] at this
  simp only [one_mul] at this
  rw [this]
  split_ifs <;> rfl

theorem degree_inl_zero (he : ∀ s, 0 < e s) :
    ∑ i, (x0MqAdj e i (Sum.inl 0) : ℤ) = Fintype.card ι := by
  have := rowSum_inl_zero e he 1 1 (fun _ _ => 1)
  rw [ofProfile_one] at this
  simp only [one_mul] at this
  rw [this]
  simp [Finset.sum_const]

theorem alpha_ofProfile_inr (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) (s : ι) (k : Fin (e s - 1)) :
    intersectionAlpha (x0MqResolvedTable e) (ofProfile e b₀ b₁ g) (Sum.inr ⟨s, k⟩) =
      (if k.val = 0 then b₀ else g s k.val) - 2 * g s (k.val + 1) +
        (if k.val + 1 < e s - 1 then g s (k.val + 1 + 1) else b₁) := by
  rw [alpha_apply, rowSum_inr, degree_inr, ofProfile_inr]
  ring

theorem alpha_ofProfile_inl_zero (he : ∀ s, 0 < e s) (b₀ b₁ : ℤ) (g : ι → ℕ → ℤ) :
    intersectionAlpha (x0MqResolvedTable e) (ofProfile e b₀ b₁ g) (Sum.inl 0) =
      ∑ s : ι, ((if 1 < e s then g s 1 else b₁) - b₀) := by
  rw [alpha_apply, rowSum_inl_zero e he, degree_inl_zero e he, ofProfile_inl_zero,
    Finset.sum_sub_distrib]
  simp [Finset.sum_const, mul_comm]

theorem sum_alpha (c : X0MqComponents e → ℤ) :
    ∑ j, intersectionAlpha (x0MqResolvedTable e) c j = 0 := by
  have := multiplicityBeta_intersectionAlpha (x0MqResolvedTable e) c
  rw [multiplicityBeta_apply] at this
  simpa [x0MqResolvedTable] using this

section PathFunctional

variable (s₀ : ι)

def pathDual (a : X0MqComponents e → ℤ) : Module.Dual ℤ (characterLattice ι) :=
  ((∑ s : ι, (∑ k : Fin (e s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) •
        (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)) +
      ((e s₀ : ℤ) * a (Sum.inl 1)) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ)).comp
    (characterLattice ι).subtype

def coeff (a : X0MqComponents e → ℤ) (s : ι) : ℤ :=
  (∑ k : Fin (e s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) +
    if s = s₀ then (e s₀ : ℤ) * a (Sum.inl 1) else 0

def dotDual (c : ι → ℤ) : Module.Dual ℤ (characterLattice ι) :=
  (∑ s : ι, c s • (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)).comp (characterLattice ι).subtype

omit [DecidableEq ι] in
theorem dotDual_apply (c : ι → ℤ) (D : characterLattice ι) :
    dotDual c D = ∑ s, c s * (D : ι → ℤ) s := by
  simp [dotDual, LinearMap.sum_apply]

theorem pathDual_apply (a : X0MqComponents e → ℤ) (D : characterLattice ι) :
    pathDual e s₀ a D = ∑ s, coeff e s₀ a s * (D : ι → ℤ) s := by
  simp only [pathDual, coeff, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, Submodule.subtype_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem pathDual_eq_dotDual (a : X0MqComponents e → ℤ) :
    pathDual e s₀ a = dotDual (coeff e s₀ a) := by
  ext D
  rw [pathDual_apply, dotDual_apply]

theorem coeff_add (a b : X0MqComponents e → ℤ) (s : ι) :
    coeff e s₀ (a + b) s = coeff e s₀ a s + coeff e s₀ b s := by
  simp only [coeff, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  split_ifs <;> ring

theorem pathDual_add (a b : X0MqComponents e → ℤ) :
    pathDual e s₀ (a + b) = pathDual e s₀ a + pathDual e s₀ b := by
  ext D
  simp only [pathDual_apply, LinearMap.add_apply, coeff_add, add_mul, Finset.sum_add_distrib]

theorem dotDual_eq_gramMap (c : ι → ℤ) (y : characterLattice ι) (κ : ℤ)
    (h : ∀ s, c s = (e s : ℤ) * (y : ι → ℤ) s + κ) : dotDual c = gramMap e y := by
  ext D
  rw [dotDual_apply, gramMap_apply]
  have hD : ∑ s, (D : ι → ℤ) s = 0 := mem_characterLattice.mp D.2
  calc ∑ s, c s * (D : ι → ℤ) s
      = ∑ s, ((e s : ℤ) * ((y : ι → ℤ) s * (D : ι → ℤ) s) + κ * (D : ι → ℤ) s) :=
        Finset.sum_congr rfl fun s _ => by rw [h s]; ring
    _ = ∑ s, (e s : ℤ) * ((y : ι → ℤ) s * (D : ι → ℤ) s) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hD, mul_zero, add_zero]

def bvec (s : ι) : characterLattice ι :=
  ⟨Pi.single s 1 - Pi.single s₀ 1, by
    rw [mem_characterLattice]
    simp [Finset.sum_sub_distrib]⟩

@[scoped simp] theorem bvec_apply (s t : ι) :
    ((bvec s₀ s : characterLattice ι) : ι → ℤ) t = (if t = s then 1 else 0) - if t = s₀ then 1 else 0 := by
  simp [bvec, Pi.single_apply]

theorem coeff_sub_of_dotDual_eq_gramMap (c : ι → ℤ) (y : characterLattice ι)
    (h : dotDual c = gramMap e y) (s : ι) :
    c s - (e s : ℤ) * (y : ι → ℤ) s = c s₀ - (e s₀ : ℤ) * (y : ι → ℤ) s₀ := by
  have := LinearMap.congr_fun h (bvec s₀ s)
  rw [dotDual_apply, gramMap_apply] at this
  simp only [bvec_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  linarith

theorem exists_dotDual_eq (φ : Module.Dual ℤ (characterLattice ι)) :
    dotDual (fun s => φ (bvec s₀ s)) = φ := by
  ext D
  rw [dotDual_apply]
  have hD : ∑ s, (D : ι → ℤ) s = 0 := mem_characterLattice.mp D.2
  have hdec : D = ∑ s, (D : ι → ℤ) s • bvec s₀ s := by
    apply Subtype.ext
    funext t
    rw [Submodule.coe_sum]
    simp only [Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, bvec_apply, smul_eq_mul,
      mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs with ht
    · rw [hD, sub_zero]
    · simp
  conv_rhs => rw [hdec]
  rw [map_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul, mul_comm]

def hgt (D : ι → ℤ) : X0MqComponents e → ℤ :=
  ofProfile e 0 ((e s₀ : ℤ) * D s₀) fun s p => (p : ℤ) * D s

theorem pathDual_apply_eq_sum_hgt (a : X0MqComponents e → ℤ) (D : characterLattice ι) :
    pathDual e s₀ a D = ∑ j, a j * hgt e s₀ (D : ι → ℤ) j := by
  rw [pathDual_apply, sum_components]
  simp only [hgt, ofProfile_inl_zero, ofProfile_inl_one, ofProfile_inr, mul_zero, zero_add]
  have hc : ∀ s, coeff e s₀ a s * (D : ι → ℤ) s =
      (∑ k : Fin (e s - 1), a (Sum.inr ⟨s, k⟩) * (((k.val + 1 : ℕ) : ℤ) * (D : ι → ℤ) s)) +
        if s = s₀ then a (Sum.inl 1) * ((e s₀ : ℤ) * (D : ι → ℤ) s₀) else 0 := by
    intro s
    rw [coeff, add_mul, Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    · split_ifs with h
      · subst h; ring
      · rw [zero_mul]
  simp only [hc, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem sum_alpha_mul_eq (f h : X0MqComponents e → ℤ) :
    ∑ j, intersectionAlpha (x0MqResolvedTable e) f j * h j =
      ∑ i, f i * intersectionAlpha (x0MqResolvedTable e) h i := by
  simp only [intersectionAlpha_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [(x0MqResolvedTable e).inter_symm i j]; ring

end PathFunctional

section Claim1

variable (s₀ : ι)

local notation "tab" => x0MqResolvedTable e

def lastv (f : X0MqComponents e → ℤ) (s : ι) : ℤ :=
  if h : 0 < e s - 1 then f (Sum.inr ⟨s, ⟨e s - 2, by omega⟩⟩) else f (Sum.inl 0)

theorem alpha_hgt_inr (D : ι → ℤ) (s : ι) (k : Fin (e s - 1)) :
    intersectionAlpha tab (hgt e s₀ D) (Sum.inr ⟨s, k⟩) =
      if k.val + 1 < e s - 1 then 0 else (e s₀ : ℤ) * D s₀ - (e s : ℤ) * D s := by
  rw [hgt, alpha_ofProfile_inr]
  have hk := k.2
  have h0 : (if k.val = 0 then (0 : ℤ) else ((k.val : ℕ) : ℤ) * D s) = (k.val : ℤ) * D s := by
    split_ifs with h
    · rw [h]; simp
    · rfl
  rw [h0]
  by_cases h1 : k.val + 1 < e s - 1
  · rw [if_pos h1, if_pos h1]; push_cast; ring
  · rw [if_neg h1, if_neg h1]
    have : (e s : ℤ) = k.val + 2 := by omega
    rw [this]; push_cast; ring

theorem sum_alpha_hgt_inr (D : ι → ℤ) (s : ι) :
    ∑ k : Fin (e s - 1), intersectionAlpha tab (hgt e s₀ D) (Sum.inr ⟨s, k⟩) =
      if 0 < e s - 1 then (e s₀ : ℤ) * D s₀ - (e s : ℤ) * D s else 0 := by
  simp only [alpha_hgt_inr]
  split_ifs with hpos
  · rw [Finset.sum_eq_single ⟨e s - 2, by omega⟩]
    · rw [if_neg]; simp only; omega
    · intro k _ hk
      rw [if_pos]
      have := k.2
      have hne : k.val ≠ e s - 2 := fun h => hk (Fin.ext h)
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun k _ => absurd k.2 (by omega)

theorem sum_mul_alpha_hgt_inr (f : X0MqComponents e → ℤ) (D : ι → ℤ) (s : ι) :
    ∑ k : Fin (e s - 1), f (Sum.inr ⟨s, k⟩) * intersectionAlpha tab (hgt e s₀ D) (Sum.inr ⟨s, k⟩) =
      if 0 < e s - 1 then lastv e f s * ((e s₀ : ℤ) * D s₀ - (e s : ℤ) * D s) else 0 := by
  simp only [alpha_hgt_inr, mul_ite, mul_zero]
  split_ifs with hpos
  · rw [Finset.sum_eq_single ⟨e s - 2, by omega⟩]
    · rw [if_neg (by simp only; omega), lastv, dif_pos hpos]
    · intro k _ hk
      rw [if_pos]
      have := k.2
      have hne : k.val ≠ e s - 2 := fun h => hk (Fin.ext h)
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun k _ => absurd k.2 (by omega)

theorem alpha_hgt_inl_zero (he : ∀ s, 0 < e s) (D : ι → ℤ) :
    intersectionAlpha tab (hgt e s₀ D) (Sum.inl 0) =
      ∑ s : ι, (if 1 < e s then D s else (e s₀ : ℤ) * D s₀) := by
  rw [hgt, alpha_ofProfile_inl_zero e he]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

theorem alpha_hgt_inl_one (he : ∀ s, 0 < e s) (D : ι → ℤ) :
    intersectionAlpha tab (hgt e s₀ D) (Sum.inl 1) =
      -(∑ s : ι, (if 1 < e s then D s else (e s₀ : ℤ) * D s₀)) -
        ∑ s : ι, (if 0 < e s - 1 then (e s₀ : ℤ) * D s₀ - (e s : ℤ) * D s else 0) := by
  have h := sum_alpha e (hgt e s₀ D)
  rw [sum_components, alpha_hgt_inl_zero e s₀ he] at h
  simp only [sum_alpha_hgt_inr] at h
  linarith

def yvec (f : X0MqComponents e → ℤ) : characterLattice ι :=
  ⟨fun s => (f (Sum.inl 1) - lastv e f s) +
      if s = s₀ then ∑ t, (lastv e f t - f (Sum.inl 1)) else 0, by
    rw [mem_characterLattice, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
      ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun s _ => by ring⟩

theorem yvec_apply (f : X0MqComponents e → ℤ) (s : ι) :
    ((yvec e s₀ f : characterLattice ι) : ι → ℤ) s =
      (f (Sum.inl 1) - lastv e f s) + if s = s₀ then ∑ t, (lastv e f t - f (Sum.inl 1)) else 0 :=
  rfl

theorem sum_mul_alpha_hgt (he : ∀ s, 0 < e s) (f : X0MqComponents e → ℤ) (D : ι → ℤ) :
    ∑ i, f i * intersectionAlpha tab (hgt e s₀ D) i =
      (f (Sum.inl 0) - f (Sum.inl 1)) * ∑ s, D s +
        ∑ s, (e s : ℤ) * (((yvec e s₀ f : characterLattice ι) : ι → ℤ) s * D s) := by
  rw [sum_components, alpha_hgt_inl_zero e s₀ he, alpha_hgt_inl_one e s₀ he]
  simp only [sum_mul_alpha_hgt_inr, yvec_apply]

  have hE : ∑ s, (e s : ℤ) * ((f (Sum.inl 1) - lastv e f s +
        if s = s₀ then ∑ t, (lastv e f t - f (Sum.inl 1)) else 0) * D s) =
      ∑ s, ((e s : ℤ) * (f (Sum.inl 1) - lastv e f s) * D s +
        (e s₀ : ℤ) * D s₀ * (lastv e f s - f (Sum.inl 1))) := by
    simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    · exact Finset.sum_congr rfl fun s _ => by ring
    · rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
  rw [hE, Finset.mul_sum, Finset.mul_sum, mul_sub, mul_neg, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := he s
  by_cases h1 : e s = 1
  · have hl : lastv e f s = f (Sum.inl 0) := by rw [lastv, dif_neg (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hl, h1]
    push_cast; ring
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    ring

theorem pathDual_alpha (he : ∀ s, 0 < e s) (f : X0MqComponents e → ℤ) :
    pathDual e s₀ (intersectionAlpha tab f) = gramMap e (yvec e s₀ f) := by
  ext D
  rw [pathDual_apply_eq_sum_hgt, sum_alpha_mul_eq, sum_mul_alpha_hgt e s₀ he, gramMap_apply,
    mem_characterLattice.mp D.2, mul_zero, zero_add]

theorem pathDual_alpha_mem_range (he : ∀ s, 0 < e s) (f : X0MqComponents e → ℤ) :
    pathDual e s₀ (intersectionAlpha tab f) ∈ LinearMap.range (gramMap e) :=
  ⟨yvec e s₀ f, (pathDual_alpha e s₀ he f).symm⟩

end Claim1

section Claim3

variable (s₀ : ι)

local notation "tab" => x0MqResolvedTable e

def apos (a : X0MqComponents e → ℤ) (s : ι) (i : ℕ) : ℤ :=
  if h : 0 < i ∧ i - 1 < e s - 1 then a (Sum.inr ⟨s, ⟨i - 1, h.2⟩⟩) else 0

omit [Fintype ι] [DecidableEq ι] in
theorem apos_zero (a : X0MqComponents e → ℤ) (s : ι) : apos e a s 0 = 0 := by
  simp [apos]

omit [Fintype ι] [DecidableEq ι] in
theorem apos_succ (a : X0MqComponents e → ℤ) (s : ι) (k : Fin (e s - 1)) :
    apos e a s (k.val + 1) = a (Sum.inr ⟨s, k⟩) := by
  have hk := k.2
  rw [apos, dif_pos ⟨Nat.succ_pos _, by simpa using hk⟩]
  congr

omit [Fintype ι] [DecidableEq ι] in
theorem apos_of_le (a : X0MqComponents e → ℤ) (s : ι) (i : ℕ) (hi : e s ≤ i) (hpos : 0 < e s) :
    apos e a s i = 0 := by
  rw [apos, dif_neg]
  omega

omit [DecidableEq ι] in

theorem sum_range_eq (he : ∀ s, 0 < e s) (s : ι) (F : ℕ → ℤ) :
    ∑ i ∈ Finset.range (e s), F i = F 0 + ∑ k : Fin (e s - 1), F (k.val + 1) := by
  have h : Finset.range (e s) = Finset.range (e s - 1 + 1) := by
    congr 1; have := he s; omega
  rw [h, Finset.sum_range_succ', Fin.sum_univ_eq_sum_range (fun i => F (i + 1)) (e s - 1), add_comm]

theorem sum_range_triangle (F : ℕ → ℤ) (n : ℕ) :
    ∑ r ∈ Finset.range n, ∑ i ∈ Finset.range (r + 1), F i =
      ∑ i ∈ Finset.range n, ((n : ℤ) - i) * F i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun i => F i) n,
      Finset.sum_range_succ (fun i => (((n + 1 : ℕ) : ℤ) - i) * F i) n]
    have : ∑ i ∈ Finset.range n, (((n + 1 : ℕ) : ℤ) - i) * F i =
        ∑ i ∈ Finset.range n, ((n : ℤ) - i) * F i + ∑ i ∈ Finset.range n, F i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [this]; push_cast; ring

variable (a : X0MqComponents e → ℤ) (y : characterLattice ι)

def massA (s : ι) : ℤ := ∑ k : Fin (e s - 1), a (Sum.inr ⟨s, k⟩)

def slope (s : ι) : ℤ :=
  -massA e a s + (y : ι → ℤ) s - if s = s₀ then a (Sum.inl 1) else 0

def delta (s : ι) (r : ℕ) : ℤ := slope e s₀ a y s + ∑ i ∈ Finset.range r, apos e a s i

def gInt (s : ι) (p : ℕ) : ℤ := ∑ r ∈ Finset.range p, delta e s₀ a y s (r + 1)

omit [DecidableEq ι] in
theorem massA_eq_sum_range (he : ∀ s, 0 < e s) (s : ι) :
    massA e a s = ∑ i ∈ Finset.range (e s), apos e a s i := by
  rw [sum_range_eq e he, apos_zero, zero_add, massA]
  exact Finset.sum_congr rfl fun k _ => (apos_succ e a s k).symm

theorem coeff_eq_sum_range (he : ∀ s, 0 < e s) (s : ι) :
    coeff e s₀ a s = (∑ i ∈ Finset.range (e s), (i : ℤ) * apos e a s i) +
      if s = s₀ then (e s₀ : ℤ) * a (Sum.inl 1) else 0 := by
  rw [coeff, sum_range_eq e he]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [apos_succ]; push_cast; ring

theorem gInt_zero (s : ι) : gInt e s₀ a y s 0 = 0 := by simp [gInt]

theorem gInt_one (s : ι) : gInt e s₀ a y s 1 = slope e s₀ a y s := by
  simp [gInt, delta, apos_zero]

theorem gInt_second_diff (s : ι) (p : ℕ) :
    gInt e s₀ a y s p - 2 * gInt e s₀ a y s (p + 1) + gInt e s₀ a y s (p + 2) = apos e a s (p + 1) := by
  simp only [gInt, delta, Finset.sum_range_succ]
  ring

theorem gInt_eq (s : ι) (n : ℕ) :
    gInt e s₀ a y s n = (n : ℤ) * slope e s₀ a y s +
      ∑ i ∈ Finset.range n, ((n : ℤ) - i) * apos e a s i := by
  simp only [gInt, delta, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, sum_range_triangle]

theorem gInt_end (he : ∀ s, 0 < e s)
    (hK : ∀ s, coeff e s₀ a s - (e s : ℤ) * (y : ι → ℤ) s =
      coeff e s₀ a s₀ - (e s₀ : ℤ) * (y : ι → ℤ) s₀) (s : ι) :
    gInt e s₀ a y s (e s) = (e s₀ : ℤ) * (y : ι → ℤ) s₀ - coeff e s₀ a s₀ := by
  have h1 := hK s
  have h2 : (e s₀ : ℤ) * (y : ι → ℤ) s₀ - coeff e s₀ a s₀ =
      (e s : ℤ) * (y : ι → ℤ) s - coeff e s₀ a s := by linarith
  rw [h2, gInt_eq, slope, massA_eq_sum_range e a he, coeff_eq_sum_range e s₀ a he s]
  have hsplit : ∑ i ∈ Finset.range (e s), ((e s : ℤ) - i) * apos e a s i =
      (e s : ℤ) * ∑ i ∈ Finset.range (e s), apos e a s i -
        ∑ i ∈ Finset.range (e s), (i : ℤ) * apos e a s i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  by_cases hs : s = s₀
  · subst hs
    simp only [if_true]
    ring
  · simp only [if_neg hs]
    ring

def fInt : X0MqComponents e → ℤ :=
  ofProfile e 0 ((e s₀ : ℤ) * (y : ι → ℤ) s₀ - coeff e s₀ a s₀) (gInt e s₀ a y)

theorem alpha_fInt (he : ∀ s, 0 < e s)
    (ha : ∑ j, a j = 0)
    (hK : ∀ s, coeff e s₀ a s - (e s : ℤ) * (y : ι → ℤ) s =
      coeff e s₀ a s₀ - (e s₀ : ℤ) * (y : ι → ℤ) s₀) :
    intersectionAlpha tab (fInt e s₀ a y) = a := by

  have hinr : ∀ (s : ι) (k : Fin (e s - 1)),
      intersectionAlpha tab (fInt e s₀ a y) (Sum.inr ⟨s, k⟩) = a (Sum.inr ⟨s, k⟩) := by
    intro s k
    have hk := k.2
    rw [fInt, alpha_ofProfile_inr]
    have h0 : (if k.val = 0 then (0 : ℤ) else gInt e s₀ a y s k.val) = gInt e s₀ a y s k.val := by
      split_ifs with h
      · rw [h, gInt_zero]
      · rfl
    have h2 : (if k.val + 1 < e s - 1 then gInt e s₀ a y s (k.val + 1 + 1)
        else (e s₀ : ℤ) * (y : ι → ℤ) s₀ - coeff e s₀ a s₀) = gInt e s₀ a y s (k.val + 2) := by
      split_ifs with h
      · rfl
      · have : k.val + 2 = e s := by omega
        rw [this, gInt_end e s₀ a y he hK s]
    rw [h0, h2, gInt_second_diff, apos_succ]

  have hinl0 : intersectionAlpha tab (fInt e s₀ a y) (Sum.inl 0) = a (Sum.inl 0) := by
    rw [fInt, alpha_ofProfile_inl_zero e he]
    have h1 : ∀ s, (if 1 < e s then gInt e s₀ a y s 1
        else (e s₀ : ℤ) * (y : ι → ℤ) s₀ - coeff e s₀ a s₀) - 0 = slope e s₀ a y s := by
      intro s
      rw [sub_zero]
      split_ifs with h
      · exact gInt_one e s₀ a y s
      · have hs : e s = 1 := by have := he s; omega
        rw [← gInt_end e s₀ a y he hK s, hs, gInt_one]
    simp only [h1, slope, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mem_characterLattice.mp y.2]
    rw [sum_components] at ha
    simp only [massA]
    linarith

  have hinl1 : intersectionAlpha tab (fInt e s₀ a y) (Sum.inl 1) = a (Sum.inl 1) := by
    have h := sum_alpha e (fInt e s₀ a y)
    rw [sum_components, hinl0] at h
    simp only [hinr] at h
    rw [sum_components] at ha
    linarith
  funext j
  rcases j with i | ⟨s, k⟩
  · fin_cases i
    · exact hinl0
    · exact hinl1
  · exact hinr s k

theorem exists_alpha_eq_of_pathDual_mem_range (he : ∀ s, 0 < e s)
    (ha : ∑ j, a j = 0) (hmem : pathDual e s₀ a ∈ LinearMap.range (gramMap e)) :
    ∃ f, intersectionAlpha tab f = a := by
  obtain ⟨y, hy⟩ := hmem
  refine ⟨fInt e s₀ a y, alpha_fInt e s₀ a y he ha fun s => ?_⟩
  rw [pathDual_eq_dotDual] at hy
  exact coeff_sub_of_dotDual_eq_gramMap e s₀ _ y hy.symm s

end Claim3

section Claim2

variable (s₀ : ι)

local notation "tab" => x0MqResolvedTable e

variable (c : ι → ℤ)

def ySurj : characterLattice ι :=
  ⟨fun t => (if t = s₀ then ∑ u, (if e u = 1 ∧ u ≠ s₀ then c u else 0) else 0) +
      (if e t = 1 ∧ t ≠ s₀ then -c t else 0), by
    rw [mem_characterLattice, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
      ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun t _ => by split_ifs <;> ring⟩

theorem ySurj_apply (t : ι) : ((ySurj e s₀ c : characterLattice ι) : ι → ℤ) t =
    (if t = s₀ then ∑ u, (if e u = 1 ∧ u ≠ s₀ then c u else 0) else 0) +
      (if e t = 1 ∧ t ≠ s₀ then -c t else 0) := rfl

def bSurj : ℤ := (∑ u, (if e u = 1 ∧ u ≠ s₀ then c u else 0)) + if e s₀ = 1 then c s₀ else 0

def aSurj : X0MqComponents e → ℤ :=
  ofProfile e (-(bSurj e s₀ c + ∑ s, ∑ k : Fin (e s - 1), (if k.val + 1 = 1 then c s else 0)))
    (bSurj e s₀ c) fun s p => if p = 1 then c s else 0

theorem sum_aSurj : ∑ j, aSurj e s₀ c j = 0 := by
  rw [sum_components]
  simp only [aSurj, ofProfile_inl_zero, ofProfile_inl_one, ofProfile_inr]
  ring

theorem coeff_aSurj (he : ∀ s, 0 < e s) (s : ι) :
    coeff e s₀ (aSurj e s₀ c) s = c s + (e s : ℤ) * ((ySurj e s₀ c : characterLattice ι) : ι → ℤ) s := by
  have hs := he s
  rw [coeff, ySurj_apply]
  simp only [aSurj, ofProfile_inr, ofProfile_inl_one]
  have hsum : ∑ k : Fin (e s - 1), ((k : ℤ) + 1) * (if k.val + 1 = 1 then c s else 0) =
      if 0 < e s - 1 then c s else 0 := by
    split_ifs with hpos
    · rw [Finset.sum_eq_single ⟨0, hpos⟩]
      · simp
      · intro k _ hk
        rw [if_neg, mul_zero]
        intro h; apply hk; ext; simp only; omega
      · intro h; exact absurd (Finset.mem_univ _) h
    · exact Finset.sum_eq_zero fun k _ => absurd k.2 (by omega)
  rw [hsum, bSurj]
  by_cases hs0 : s = s₀
  · subst hs0
    simp only [if_true, ne_eq, not_true_eq_false, and_false, if_false, add_zero]
    by_cases h1 : e s = 1
    · rw [if_neg (by omega), if_pos h1, h1]; push_cast; ring
    · rw [if_pos (by omega), if_neg h1]; ring
  · rw [if_neg hs0, if_neg hs0, zero_add, add_zero]
    by_cases h1 : e s = 1
    · rw [if_neg (by omega), if_pos ⟨h1, hs0⟩, h1]; push_cast; ring
    · rw [if_pos (by omega), if_neg (fun h => h1 h.1)]; ring

theorem pathDual_aSurj (he : ∀ s, 0 < e s) :
    pathDual e s₀ (aSurj e s₀ c) = dotDual c + gramMap e (ySurj e s₀ c) := by
  ext D
  rw [pathDual_apply, LinearMap.add_apply, dotDual_apply, gramMap_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [coeff_aSurj e s₀ c he]; ring

end Claim2

section Assembly

variable (s₀ : ι) (he : ∀ s, 0 < e s)

local notation "tab" => x0MqResolvedTable e

omit [DecidableEq ι] in
theorem componentGroupProj_eq_zero_iff (φ : Module.Dual ℤ (characterLattice ι)) :
    componentGroupProj e φ = 0 ↔ φ ∈ LinearMap.range (gramMap e) :=
  Submodule.Quotient.mk_eq_zero _

omit [DecidableEq ι] in
theorem componentGroupProj_surjective : Function.Surjective (componentGroupProj e) :=
  Submodule.mkQ_surjective _

def psi0 : (X0MqComponents e → ℤ) →+ componentGroup e where
  toFun a := componentGroupProj e (pathDual e s₀ a)
  map_zero' := by
    have : pathDual e s₀ (0 : X0MqComponents e → ℤ) = 0 := by
      ext D; simp [pathDual_apply, coeff]
    rw [this, map_zero]
  map_add' a b := by rw [pathDual_add, map_add]

theorem psi0_apply (a : X0MqComponents e → ℤ) :
    psi0 e s₀ a = componentGroupProj e (pathDual e s₀ a) := rfl

include he in
theorem psi0_alpha (f : X0MqComponents e → ℤ) : psi0 e s₀ (intersectionAlpha tab f) = 0 := by
  rw [psi0_apply, componentGroupProj_eq_zero_iff]
  exact pathDual_alpha_mem_range e s₀ he f

def psi : AppendixComponentGroup tab →+ componentGroup e :=
  QuotientAddGroup.lift (imageOfIntersectionAlpha tab)
    ((psi0 e s₀).comp (degreeZeroSublattice tab).subtype) (by
      intro x hx
      obtain ⟨c, hc⟩ := mem_imageOfIntersectionAlpha.mp hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, ← hc]
      exact psi0_alpha e s₀ he c)

theorem psi_class (a : X0MqComponents e → ℤ) (ha : a ∈ degreeZeroSublattice tab) :
    psi e s₀ he (appendixComponentGroupClass tab ⟨a, ha⟩) = componentGroupProj e (pathDual e s₀ a) :=
  rfl

include he in
theorem psi_injective : Function.Injective (psi e s₀ he) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨a, ha⟩ := x
    have hx' : componentGroupProj e (pathDual e s₀ a) = 0 := by
      rw [← psi_class e s₀ he a ha]; exact hx
    rw [componentGroupProj_eq_zero_iff] at hx'
    have hsum : ∑ j, a j = 0 := by
      have := mem_degreeZeroSublattice.mp ha
      simpa [x0MqResolvedTable] using this
    obtain ⟨f, hf⟩ := exists_alpha_eq_of_pathDual_mem_range e s₀ a he hsum hx'
    exact (QuotientAddGroup.eq_zero_iff _).mpr (mem_imageOfIntersectionAlpha.mpr ⟨f, hf⟩)

include he in
theorem psi_surjective : Function.Surjective (psi e s₀ he) := by
  intro z
  obtain ⟨φ, rfl⟩ := componentGroupProj_surjective e z
  let c : ι → ℤ := fun s => φ (bvec s₀ s)
  have ha : aSurj e s₀ c ∈ degreeZeroSublattice tab := by
    rw [mem_degreeZeroSublattice]
    simpa [x0MqResolvedTable] using sum_aSurj e s₀ c
  refine ⟨appendixComponentGroupClass tab ⟨aSurj e s₀ c, ha⟩, ?_⟩
  rw [psi_class, pathDual_aSurj e s₀ c he, exists_dotDual_eq, map_add,
    (componentGroupProj_eq_zero_iff e _).mpr ⟨_, rfl⟩, add_zero]

noncomputable def psiEquiv : AppendixComponentGroup tab ≃+ componentGroup e :=
  AddEquiv.ofBijective (psi e s₀ he) ⟨psi_injective e s₀ he, psi_surjective e s₀ he⟩

theorem psiEquiv_class (a : X0MqComponents e → ℤ) (ha : a ∈ degreeZeroSublattice tab) :
    psiEquiv e s₀ he (appendixComponentGroupClass tab ⟨a, ha⟩) =
      componentGroupProj e (pathDual e s₀ a) :=
  rfl

theorem branchDiff_mem :
    (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inl 0) 1 : X0MqComponents e → ℤ) ∈
      degreeZeroSublattice tab := by
  rw [mem_degreeZeroSublattice]
  simp [x0MqResolvedTable, Finset.sum_sub_distrib]

theorem pathDual_branchDiff :
    pathDual e s₀ (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inl 0) 1 : X0MqComponents e → ℤ) =
      (e s₀ : ℤ) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype := by
  ext D
  rw [pathDual_apply]
  simp only [coeff, Pi.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply, smul_eq_mul]
  have h1 : ∀ (s : ι) (k : Fin (e s - 1)),
      (Pi.single (Sum.inl 1) (1 : ℤ) : X0MqComponents e → ℤ) (Sum.inr ⟨s, k⟩) -
        (Pi.single (Sum.inl 0) (1 : ℤ) : X0MqComponents e → ℤ) (Sum.inr ⟨s, k⟩) = 0 := by
    intro s k
    rw [Pi.single_eq_of_ne (by simp), Pi.single_eq_of_ne (by simp), sub_zero]
  have h2 : (Pi.single (Sum.inl 1) (1 : ℤ) : X0MqComponents e → ℤ) (Sum.inl 1) -
      (Pi.single (Sum.inl 0) (1 : ℤ) : X0MqComponents e → ℤ) (Sum.inl 1) = 1 := by
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (by simp), sub_zero]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add, mul_one, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Assembly

end NeronObjPathIso
p2m_reactivate "P2MW.S_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj.NeronObjPathIso"

open NeronObjPathIso in

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ) (he : ∀ x, 0 < e x) (s₀ : ι) :
    ∃ ψ : AppendixComponentGroup (x0MqResolvedTable e) ≃+ componentGroup e,
      (∀ (a : X0MqComponents e → ℤ) (ha : a ∈ degreeZeroSublattice (x0MqResolvedTable e)),
        ψ (appendixComponentGroupClass (x0MqResolvedTable e) ⟨a, ha⟩) =
          componentGroupProj e
            (((∑ s : ι, (∑ k : Fin (e s - 1), ((k : ℤ) + 1) * a (Sum.inr ⟨s, k⟩)) •
                  (LinearMap.proj s : (ι → ℤ) →ₗ[ℤ] ℤ)) +
                ((e s₀ : ℤ) * a (Sum.inl 1)) • (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ)).comp
              (characterLattice ι).subtype)) ∧
      ∃ hb : (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inl 0) 1 : X0MqComponents e → ℤ) ∈
          degreeZeroSublattice (x0MqResolvedTable e),
        ψ (appendixComponentGroupClass (x0MqResolvedTable e) ⟨_, hb⟩) =
          componentGroupProj e ((e s₀ : ℤ) •
            (LinearMap.proj s₀ : (ι → ℤ) →ₗ[ℤ] ℤ).comp (characterLattice ι).subtype) := by
  refine ⟨psiEquiv e s₀ he, fun a ha => psiEquiv_class e s₀ he a ha, branchDiff_mem e, ?_⟩
  rw [psiEquiv_class, pathDual_branchDiff]

end S_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj
end P2MW
export P2MW.S_ModularCurve_exists_addEquiv_appendixComponentGroup_x0MqResolvedTable_apply_eq_componentGroupProj (solution)
