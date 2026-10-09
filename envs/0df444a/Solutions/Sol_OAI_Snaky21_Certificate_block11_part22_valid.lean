-- Prove2me | solution 1 for OAI.Snaky21.Certificate.block11_part22_valid
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:29:29.38008+00:00
-- url     : https://prove2.me/submissions/77a462bc-1c14-4eeb-b57f-e5c8b693ee5f

import Theorems.Thm_OAI_Snaky21_Certificate_block07_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part05_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part06_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part11_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part13_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part14_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part20_valid
import Definitions.Def_Snaky21Calc11Part11
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block10_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block11_part21_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate
namespace OAI.Snaky21
theorem base_valid (i : Fin 6) : Valid (baseCard i) := claim_calculus.1 i
theorem placed_valid (r : Fin 8) (t : Cell) {c : Card} (h : Valid c) : Valid (placed r t c) := claim_calculus.2.1 r t c h
end OAI.Snaky21

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.Snaky21.Certificate
theorem computed_card_ext {c d : Card} (hA : c.required = d.required) (hT : c.envelope = d.envelope) (hh : c.height = d.height) : c = d := by
  cases c
  cases d
  cases hA
  cases hT
  cases hh
  rfl
theorem valid_459 : Valid card_459 := block07_valid.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_579 : Valid card_579 := block09_valid.2.2.2.1
theorem valid_581 : Valid card_581 := block09_valid.2.2.2.2.2.1
theorem valid_654 : Valid card_654 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_661 : Valid card_661 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_677 : Valid card_677 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_682 : Valid card_682 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_694 : Valid card_694 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_696 : Valid card_696 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_698 : Valid card_698 := block10_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem valid_709 : Valid card_709 := block11_part05_valid.1
theorem valid_710 : Valid card_710 := block11_part06_valid.1
theorem valid_715 : Valid card_715 := block11_part11_valid.1
theorem valid_717 : Valid card_717 := block11_part13_valid.1
theorem valid_718 : Valid card_718 := block11_part14_valid.1
theorem valid_724 : Valid card_724 := block11_part20_valid.1

theorem calc11_card_2234_eq : placed 1 (3, 6) card_459 = calc11_card_2234 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2235_eq : placed 2 (6, 11) card_579 = calc11_card_2235 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2236_eq : placed 1 (3, 3) card_581 = calc11_card_2236 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2237_eq : placed 1 (4, 4) card_654 = calc11_card_2237 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2238_eq : placed 3 (12, 3) card_661 = calc11_card_2238 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2239_eq : placed 5 (3, 10) card_677 = calc11_card_2239 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2240_eq : placed 2 (4, 12) card_682 = calc11_card_2240 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2241_eq : placed 1 (2, 2) card_694 = calc11_card_2241 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2242_eq : placed 3 (13, 2) card_696 = calc11_card_2242 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2243_eq : placed 5 (3, 11) card_698 = calc11_card_2243 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2244_eq : placed 3 (13, 2) card_709 = calc11_card_2244 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2245_eq : placed 3 (12, 4) card_710 = calc11_card_2245 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2246_eq : placed 0 (3, 2) card_715 = calc11_card_2246 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2247_eq : placed 2 (3, 13) card_717 = calc11_card_2247 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2248_eq : placed 3 (13, 2) card_718 = calc11_card_2248 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2249_eq : placed 3 (15, 2) card_724 = calc11_card_2249 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2250_eq : calc11_card_2249.required ∪ ∅ = calc11_set_2250 := by decide +kernel

theorem calc11_set_2251_eq : calc11_card_2249.envelope ∪ ∅ = calc11_set_2251 := by decide +kernel

theorem calc11_set_2252_eq : calc11_card_2248.required ∪ calc11_set_2250 = calc11_set_2252 := by decide +kernel

theorem calc11_set_2253_eq : calc11_card_2248.envelope ∪ calc11_set_2251 = calc11_set_2253 := by decide +kernel

theorem calc11_set_2254_eq : calc11_card_2247.required ∪ calc11_set_2252 = calc11_set_2254 := by decide +kernel

theorem calc11_set_2255_eq : calc11_card_2247.envelope ∪ calc11_set_2253 = calc11_set_2255 := by decide +kernel

theorem calc11_set_2256_eq : calc11_card_2246.required ∪ calc11_set_2254 = calc11_set_2256 := by decide +kernel

theorem calc11_set_2257_eq : calc11_card_2246.envelope ∪ calc11_set_2255 = calc11_set_2257 := by decide +kernel

theorem calc11_set_2258_eq : calc11_card_2245.required ∪ calc11_set_2256 = calc11_set_2258 := by decide +kernel

theorem calc11_set_2259_eq : calc11_card_2245.envelope ∪ calc11_set_2257 = calc11_set_2259 := by decide +kernel

theorem calc11_set_2260_eq : calc11_card_2244.required ∪ calc11_set_2258 = calc11_set_2260 := by decide +kernel

theorem calc11_set_2261_eq : calc11_card_2244.envelope ∪ calc11_set_2259 = calc11_set_2261 := by decide +kernel

theorem calc11_set_2262_eq : calc11_card_2243.required ∪ calc11_set_2260 = calc11_set_2262 := by decide +kernel

theorem calc11_set_2263_eq : calc11_card_2243.envelope ∪ calc11_set_2261 = calc11_set_2263 := by decide +kernel

theorem calc11_set_2264_eq : calc11_card_2242.required ∪ calc11_set_2262 = calc11_set_2264 := by decide +kernel

theorem calc11_set_2265_eq : calc11_card_2242.envelope ∪ calc11_set_2263 = calc11_set_2265 := by decide +kernel

theorem calc11_set_2266_eq : calc11_card_2241.required ∪ calc11_set_2264 = calc11_set_2266 := by decide +kernel

theorem calc11_set_2267_eq : calc11_card_2241.envelope ∪ calc11_set_2265 = calc11_set_2267 := by decide +kernel

theorem calc11_set_2268_eq : calc11_card_2240.required ∪ calc11_set_2266 = calc11_set_2268 := by decide +kernel

theorem calc11_set_2269_eq : calc11_card_2240.envelope ∪ calc11_set_2267 = calc11_set_2269 := by decide +kernel

theorem calc11_set_2270_eq : calc11_card_2239.required ∪ calc11_set_2268 = calc11_set_2270 := by decide +kernel

theorem calc11_set_2271_eq : calc11_card_2239.envelope ∪ calc11_set_2269 = calc11_set_2271 := by decide +kernel

theorem calc11_set_2272_eq : calc11_card_2238.required ∪ calc11_set_2270 = calc11_set_2272 := by decide +kernel

theorem calc11_set_2273_eq : calc11_card_2238.envelope ∪ calc11_set_2271 = calc11_set_2273 := by decide +kernel

theorem calc11_set_2274_eq : calc11_card_2237.required ∪ calc11_set_2272 = calc11_set_2274 := by decide +kernel

theorem calc11_set_2275_eq : calc11_card_2237.envelope ∪ calc11_set_2273 = calc11_set_2275 := by decide +kernel

theorem calc11_set_2276_eq : calc11_card_2236.required ∪ calc11_set_2274 = calc11_set_2276 := by decide +kernel

theorem calc11_set_2277_eq : calc11_card_2236.envelope ∪ calc11_set_2275 = calc11_set_2277 := by decide +kernel

theorem calc11_set_2278_eq : calc11_card_2235.required ∪ calc11_set_2276 = calc11_set_2278 := by decide +kernel

theorem calc11_set_2279_eq : calc11_card_2235.envelope ∪ calc11_set_2277 = calc11_set_2279 := by decide +kernel

theorem calc11_set_2280_eq : calc11_card_2234.required ∪ calc11_set_2278 = calc11_set_2280 := by decide +kernel

theorem calc11_set_2281_eq : calc11_card_2234.envelope ∪ calc11_set_2279 = calc11_set_2281 := by decide +kernel

theorem calc11_set_2282_eq : calc11_card_2249.envelope ∩ calc11_card_2234.envelope = calc11_set_2282 := by decide +kernel

theorem calc11_set_2283_eq : calc11_card_2248.envelope ∩ calc11_set_2282 = calc11_set_2283 := by decide +kernel

theorem calc11_set_2284_eq : calc11_card_2247.envelope ∩ calc11_set_2283 = calc11_set_2284 := by decide +kernel

theorem calc11_set_2285_eq : calc11_card_2246.envelope ∩ calc11_set_2284 = calc11_set_2285 := by decide +kernel

theorem calc11_set_2286_eq : calc11_card_2245.envelope ∩ calc11_set_2285 = calc11_set_2286 := by decide +kernel

theorem calc11_set_2287_eq : calc11_card_2244.envelope ∩ calc11_set_2286 = calc11_set_2287 := by decide +kernel

theorem calc11_set_2288_eq : calc11_card_2243.envelope ∩ calc11_set_2287 = calc11_set_2288 := by decide +kernel

theorem calc11_set_2289_eq : calc11_card_2242.envelope ∩ calc11_set_2288 = calc11_set_2289 := by decide +kernel

theorem calc11_set_2290_eq : calc11_card_2241.envelope ∩ calc11_set_2289 = calc11_set_2290 := by decide +kernel

theorem calc11_set_2291_eq : calc11_card_2240.envelope ∩ calc11_set_2290 = calc11_set_2291 := by decide +kernel

theorem calc11_set_2292_eq : calc11_card_2239.envelope ∩ calc11_set_2291 = calc11_set_2292 := by decide +kernel

theorem calc11_set_2293_eq : calc11_card_2238.envelope ∩ calc11_set_2292 = calc11_set_2293 := by decide +kernel

theorem calc11_set_2294_eq : calc11_card_2237.envelope ∩ calc11_set_2293 = calc11_set_2294 := by decide +kernel

theorem calc11_set_2295_eq : calc11_card_2236.envelope ∩ calc11_set_2294 = calc11_set_2295 := by decide +kernel

theorem calc11_set_2296_eq : calc11_card_2235.envelope ∩ calc11_set_2295 = calc11_set_2296 := by decide +kernel

theorem calc11_set_2297_eq : calc11_set_2280 ∪ calc11_set_2296 = calc11_set_2297 := by decide +kernel

theorem calc11_finishA_2298 : calc11_set_2297.erase (8, 7) = card_726.required := by decide +kernel

theorem calc11_finishT_2298 : insert (8, 7) calc11_set_2281 = card_726.envelope := by decide +kernel

theorem eq_card_726 : card_726 = combine (8, 7) [placed 1 (3, 6) card_459, placed 2 (6, 11) card_579, placed 1 (3, 3) card_581, placed 1 (4, 4) card_654, placed 3 (12, 3) card_661, placed 5 (3, 10) card_677, placed 2 (4, 12) card_682, placed 1 (2, 2) card_694, placed 3 (13, 2) card_696, placed 5 (3, 11) card_698, placed 3 (13, 2) card_709, placed 3 (12, 4) card_710, placed 0 (3, 2) card_715, placed 2 (3, 13) card_717, placed 3 (13, 2) card_718, placed 3 (15, 2) card_724] := by
  rw [calc11_card_2234_eq, calc11_card_2235_eq, calc11_card_2236_eq, calc11_card_2237_eq, calc11_card_2238_eq, calc11_card_2239_eq, calc11_card_2240_eq, calc11_card_2241_eq, calc11_card_2242_eq, calc11_card_2243_eq, calc11_card_2244_eq, calc11_card_2245_eq, calc11_card_2246_eq, calc11_card_2247_eq, calc11_card_2248_eq, calc11_card_2249_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2250_eq, calc11_set_2252_eq, calc11_set_2254_eq, calc11_set_2256_eq, calc11_set_2258_eq, calc11_set_2260_eq, calc11_set_2262_eq, calc11_set_2264_eq, calc11_set_2266_eq, calc11_set_2268_eq, calc11_set_2270_eq, calc11_set_2272_eq, calc11_set_2274_eq, calc11_set_2276_eq, calc11_set_2278_eq, calc11_set_2280_eq, calc11_set_2282_eq, calc11_set_2283_eq, calc11_set_2284_eq, calc11_set_2285_eq, calc11_set_2286_eq, calc11_set_2287_eq, calc11_set_2288_eq, calc11_set_2289_eq, calc11_set_2290_eq, calc11_set_2291_eq, calc11_set_2292_eq, calc11_set_2293_eq, calc11_set_2294_eq, calc11_set_2295_eq, calc11_set_2296_eq, calc11_set_2297_eq, calc11_finishA_2298]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2251_eq, calc11_set_2253_eq, calc11_set_2255_eq, calc11_set_2257_eq, calc11_set_2259_eq, calc11_set_2261_eq, calc11_set_2263_eq, calc11_set_2265_eq, calc11_set_2267_eq, calc11_set_2269_eq, calc11_set_2271_eq, calc11_set_2273_eq, calc11_set_2275_eq, calc11_set_2277_eq, calc11_set_2279_eq, calc11_set_2281_eq, calc11_finishT_2298]
  · decide +kernel

theorem valid_726 : Valid card_726 := by
  rw [eq_card_726]
  apply combination_rule (8, 7) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 6) valid_459
  rcases hc with rfl | hc
  · exact placed_valid 2 (6, 11) valid_579
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_581
  rcases hc with rfl | hc
  · exact placed_valid 1 (4, 4) valid_654
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 3) valid_661
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 10) valid_677
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 12) valid_682
  rcases hc with rfl | hc
  · exact placed_valid 1 (2, 2) valid_694
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 2) valid_696
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 11) valid_698
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 2) valid_709
  rcases hc with rfl | hc
  · exact placed_valid 3 (12, 4) valid_710
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 2) valid_715
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 13) valid_717
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 2) valid_718
  subst c
  exact placed_valid 3 (15, 2) valid_724


end OAI.Snaky21.Certificate

theorem solution : Valid card_726 ∧ True :=
  ⟨valid_726, True.intro⟩
